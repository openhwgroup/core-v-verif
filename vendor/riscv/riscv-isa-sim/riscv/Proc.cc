#include "Proc.h"
#include "disasm.h"
#include "extension.h"
#include "arith.h"
#include "common.h"
#include "config.h"
#include "decode_macros.h"
#include <algorithm>
#include <assert.h>
#include <cinttypes>
#include <cmath>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits.h>
#include <stdexcept>
#include <string>

namespace openhw {
st_rvfi Processor::step(size_t n, st_rvfi reference_) {
  st_rvfi rvfi;

  this->reference = & reference_;

  bool unified_traps = (this->params[base + "unified_traps"]).a_bool;
  bool interrupts_injection = (this->params[base + "interrupts_injection"]).a_bool;
  bool debug_injection = (this->params[base + "debug_injection"]).a_bool;
  // Use mstatus as a reference
  bool inverse_csr_access = (reference->csr_addr[0x300] != 0x300);
#define INDEX_CSR(INDEX) (inverse_csr_access) ? CSR_MAX_SIZE-1-INDEX : INDEX

  memset(&rvfi, 0, sizeof(st_rvfi));

  do {
    // First intr of the trap handler
    if (this->taken_trap) {
        rvfi.intr = 1;
        if (this->which_trap >> 31) {
            this->get_state()->mip->backdoor_write(0);
        }
    }

    rvfi.pc_rdata = this->get_state()->pc;

    if (this->is_waiting_for_interrupt())
        this->clear_waiting_for_interrupt();

    if (reference->intr && interrupts_injection && !this->taken_trap) {
        // We need to ensure this is an interrupt to inject mip
        if (reference->csr_rdata[INDEX_CSR(CSR_MCAUSE)] >> 31) {
            uint64_t mip = this->mcause_to_mip(reference->csr_rdata[INDEX_CSR(CSR_MCAUSE)]);
            this->get_state()->mip->backdoor_write(mip);
            this->interrupt_injected = true;
        }
    }

    if (reference->trap && debug_injection && !this->halted()) {
        uint64_t cause = reference->csr_rdata[INDEX_CSR(CSR_DCSR)] >> 6;
        cause = cause & 0b111;
        switch (cause) {
            case 0x3:
                halt_request = HR_REGULAR;
                break;
            default:
                break;
        }
    }

    this->taken_trap = false;
    this->which_trap = 0;

    processor_t::step(n);

    this->interrupt_injected = false;

    if (this->taken_trap) {
        if (this->which_trap >> 31) {
            rvfi.intr = this->taken_trap;
            rvfi.intr |= (this->which_trap << 1);
        }
        else {
            rvfi.trap = this->taken_trap;
            rvfi.trap |= (this->which_trap << 1);
        }
    }

    rvfi.mode = this->get_state()->last_inst_priv;
    rvfi.insn =
        (uint32_t)(this->get_state()->last_inst_fetched.bits() & 0xffffffffULL);

    // TODO FIXME Handle multiple/zero writes in a single insn.
    auto &reg_commits = this->get_state()->log_reg_write;
    int xlen = this->get_state()->last_inst_xlen;
    int flen = this->get_state()->last_inst_flen;

    rvfi.rs1_addr = this->get_state()->last_inst_fetched.rs1();
    // TODO add rs1_value
    rvfi.rs2_addr = this->get_state()->last_inst_fetched.rs2();
    // TODO add rs2_value

    bool got_commit = false;
    for (auto &reg : reg_commits) {
        if ((reg.first >> 4) > 32) {
            if ((reg.first >> 4) < 0xFFF) {
                reg_t addr = reg.first >> 4;
                rvfi.csr_valid[INDEX_CSR(addr)] = 1;
                rvfi.csr_addr [INDEX_CSR(addr)] = addr;
                rvfi.csr_wdata[INDEX_CSR(addr)] = reg.second.v[0];
                rvfi.csr_wmask[INDEX_CSR(addr)] = -1;
            }
        }
        else {
            // TODO FIXME Take into account the XLEN/FLEN for int/FP values.
            rvfi.rd1_addr = reg.first >> 4;
            rvfi.rd1_wdata = reg.second.v[0];
            // TODO FIXME Handle multiple register commits per cycle.
            // TODO FIXME This must be handled on the RVFI side as well.
        }
    }

    if (csr_counters_injection) {
      // Inject values comming from the reference
      if ((rvfi.insn & MASK_CSRRS) == MATCH_CSRRS ||
          (rvfi.insn & MASK_CSRRSI) == MATCH_CSRRSI ||
          (rvfi.insn & MASK_CSRRC) == MATCH_CSRRC ||
          (rvfi.insn & MASK_CSRRCI) == MATCH_CSRRCI ||
          (rvfi.insn & MASK_CSRRW) == MATCH_CSRRW ||
          (rvfi.insn & MASK_CSRRWI) == MATCH_CSRRWI ) {

          reg_t read_csr = this->get_state()->last_inst_fetched.csr();
          switch (read_csr) {
          case CSR_MIP: // MIP
          case 0xC00: // cycle
          case 0xC80: // cycleh
          case 0xB00: // mcycle
          case 0xB80: // mcycleh

            if (reference->rd1_addr) {
              this->set_XPR(reference->rd1_addr, reference->rd1_wdata);
              rvfi.rd1_wdata = reference->rd1_wdata;
            }

            // If it is set or clear we need to inject also the value in the CSR
            if ((rvfi.insn & MASK_CSRRC) == MATCH_CSRRC ||
                (rvfi.insn & MASK_CSRRS) == MATCH_CSRRS) {
                if (reference->csr_valid[read_csr]) {
                    this->put_csr(read_csr, reference->csr_wdata[read_csr]);
                    rvfi.csr_wdata[read_csr] = reference->csr_wdata[read_csr];
                }
            }
            break;
          default:
            break;
          }
      }
    }

    // Remove sign extension applied by Spike in 32b mode.
    if (this->get_xlen() == 32) {
      rvfi.pc_rdata &= 0xffffffffULL;
      rvfi.rd1_wdata &= 0xffffffffULL;
    }

  } while (unified_traps && this->taken_trap == true && (this->which_trap >> 31));

  return rvfi;
}

Processor::Processor(
    const isa_parser_t *isa, const cfg_t *cfg, simif_t *sim, uint32_t id,
    bool halt_on_reset, FILE *log_file, std::ostream &sout_,
    Params &params_) // because of command line option --log and -s we need both
    : processor_t::processor_t(isa, cfg, sim, id, halt_on_reset, log_file,
                               sout_) {

  std::map<string, bool> registered_extensions_v;
  registered_extensions_v["cv32a60x"] = false;
  registered_extensions_v["cvxif"] = false;

  base = "/top/core/" + std::to_string(id) + "/";
  Processor::default_params(base, this->params);
  Params::parse_params(base, this->params, params_);

  string isa_str = this->params[base + "isa"].a_string;
  string priv_str = this->params[base + "priv"].a_string;
  this->isa =
      (const isa_parser_t *)new isa_parser_t(isa_str.c_str(), priv_str.c_str());
  std::cout << "[SPIKE] Proc 0 | ISA: " << isa_str << " PRIV: " << priv_str << std::endl;
  std::cout << "[SPIKE]     Non standard interrupts " << this->params[base + "non_standard_interrupts"].a_bool << std::endl;

  ((cfg_t *)cfg)->priv = priv_str.c_str();

  uint64_t trigger_count = this->params[base + "trigger_count"].a_uint64_t;
  ((cfg_t *)cfg)->trigger_count = trigger_count;

  disassembler = new disassembler_t(this->isa);

  for (auto e : this->isa->get_extensions()) {
    register_extension(e.second);
  }

  processor_t::set_pmp_num(this->params[base + "pmpregions"].a_uint64_t);

  ((cfg_t *)cfg)->misaligned =
      (this->params[base + "misaligned"]).a_bool;


  this->csr_counters_injection =
      (this->params[base + "csr_counters_injection"]).a_bool;
  string extensions_str =
      (this->params[base + "extensions"]).a_string;

  string delimiter = ",";

  extensions_str = extensions_str + delimiter;

  size_t found = extensions_str.rfind(delimiter);

  while (found != string::npos) {
    string token = extensions_str.substr(0, found);
    extensions_str = extensions_str.substr(found + delimiter.length(), extensions_str.length());
    if (token != "") {
      auto it = registered_extensions_v.find(token);
      if (it != registered_extensions_v.end()) {
        std::cout << "[SPIKE] Activating extension: " << token << std::endl;
        it->second = true;
      }
      else
        std::cout << "[SPIKE] Extension \"" << token << "\" can not be registered"
                  << std::endl;
    }
    found = extensions_str.rfind(delimiter);
  }

  for (auto ext : registered_extensions_v) {
    if (ext.second) {
      extension_t *extension = find_extension(ext.first.c_str())();
      this->register_extension(extension);
      extension->reset();
    }
  }

  this->reset();
}

void Processor::take_trap(trap_t &t, reg_t epc) {
  this->taken_trap = true;
  this->which_trap = t.cause();
  processor_t::take_trap(t, epc);
}

Processor::~Processor() {
    delete this->isa;
    for (auto e : this->custom_extensions)
        delete e.second;
}

void Processor::default_params(string base, openhw::Params &params) {
  params.set_string(base, "isa", "RV32GC", "RV32GC",
             "ISA");
  params.set_string(base, "priv", DEFAULT_PRIV, DEFAULT_PRIV, "Privilege Level");
  params.set_uint64_t(base, "boot_addr", 0x80000000UL, "0x80000000UL",
             "First PC of the core");
  params.set_string(base, "mmu_mode", "sv39", "sv39",
             "Memory virtualization mode");

  params.set_uint64_t(base, "pmpregions", 0x0UL, "0x0",
             "Number of PMP regions");
  params.set_uint64_t(base, "pmpaddr0", 0x0UL, "0x0",
             "Default PMPADDR0 value");
  params.set_uint64_t(base, "pmpcfg0", 0x0UL, "0x0",
             "Default PMPCFG0 value");
  params.set_uint64_t(base, "marchid", 0x3UL, "0x3", "MARCHID value");
  params.set_uint64_t(base, "mhartid", 0x0UL, "0x0", "MHARTID value");
  params.set_uint64_t(base, "mvendorid", 0x00000602UL, "0x00000602UL",
             "MVENDORID value");
  params.set_string(base, "extensions", "", "", "Possible extensions: cv32a60x, cvxif");

  params.set_bool(base, "status_fs_field_we_enable", false, "false",
             "XSTATUS CSR FS Write Enable param enable");
  params.set_bool(base, "status_fs_field_we", false, "false",
             "XSTATUS CSR FS Write Enable");
  params.set_bool(base, "status_vs_field_we_enable", false, "false",
             "XSTATUS CSR VS Write Enable param enable");
  params.set_bool(base, "status_vs_field_we", false, "false",
             "XSTATUS CSR VS Write Enable");
  params.set_bool(base, "status_xs_field_we_enable", (false), "false",
             "XSTATUS CSR XS Write Enable param enable");
  params.set_bool(base, "status_xs_field_we", (false), "false",
             "XSTATUS CSR XS Write Enable");

  params.set_bool(base, "misaligned", false, "false",
             "Support for misaligned memory operations");

  params.set_bool(base, "csr_counters_injection", false, "false",
             "Allow to set CSRs getting values from DPI");

  params.set_bool(base, "interrupts_injection", true, "true",
             "Allow to set MIP csr with values from DPI");

  params.set_bool(base, "debug_injection", true, "true",
             "Allow to enter in debug mode with values from DPI");

  params.set_bool(base, "hide_csrs_based_on_priv", false, "false",
             "Allow to hide CSRs based on priv modes available.");

  params.set_uint64_t(base, "mtvec_vectored_alignment", 0x4UL, "0x4",
             "Default alignment for mtvec when vector mode active");

  params.set_bool(base, "override_custom_extensions", true, "false",
             "Allow to override custom extensions value.");

  params.set_bool(base, "override_custom_extensions_value", false, "false",
             "Value for the custom extensions override.");

  params.set_bool(base, "non_standard_interrupts", false, "false",
             "Value for the custom extensions override.");

  params.set_bool(base, "unified_traps", false, "false",
             "Unify all kind of traps with the exceptions.");

  params.set_uint64_t(base, "nmi_mcause", 0x00000020, "0x00000020",
             "Value of MCAUSE in case of NMI. It does not include the interrupt bit.");

  for (auto it = Processor::csr_params.begin(); it != Processor::csr_params.end(); it++) {
      string csr_name = it->second.name;
      if (it->second.override_mask_param) {
        params.set_uint64_t(base, csr_name + "_override_value", (0x0UL), "0x0",
                    csr_name + " CSR override value");
        params.set_uint64_t(base, csr_name + "_override_mask", (0x0UL), "0x0",
                    csr_name + " CSR override mask");
      }
      if (it->second.presence_param) {
        params.set_bool(base, csr_name + "_presence", true, "true",
                    csr_name + " CSR presence");
      }
      if (it->second.write_enable_param) {
        params.set_bool(base, csr_name + "_we_enable", false, "false",
                    csr_name +" CSR Write Enable param enable");
        params.set_bool(base, csr_name + "_we", false, "false",
                    csr_name + " CSR Write Enable value");
      }
  }

  params.set_uint64_t(base, "trigger_count", 0x0000004, "0x00000004",
             "Number of enabled triggers");

}

inline void Processor::set_XPR(reg_t num, reg_t value) {
  this->state.XPR.write(num, value);
}

inline void Processor::set_FPR(reg_t num, float128_t value) {
  this->state.FPR.write(num, value);
}

void Processor::put_csr(int which, reg_t val)
{
  val = zext_xlen(val);
  auto search = state.csrmap.find(which);
  if (search != state.csrmap.end()) {
    search->second->write(val);
    return;
  }
}

reg_t Processor::get_csr(int which, insn_t insn, bool write, bool peek)
{
  auto search = get_state()->csrmap.find(which);
  if (search != state.csrmap.end()) {
    search->second->custom_checks(insn, write);
    if (!peek) {
      search->second->verify_permissions(insn, write);
    }
    return search->second->read();
  }
  // If we get here, the CSR doesn't exist.  Unimplemented CSRs always throw
  // illegal-instruction exceptions, not virtual-instruction exceptions.
  throw trap_illegal_instruction(insn.bits());
}

void Processor::reset()
{
    processor_t::reset();

    uint64_t new_pc = (this->params[base + "boot_addr"]).a_uint64_t;
    this->state.pc = new_pc;

    this->put_csr(CSR_PMPADDR0, (this->params[base + "pmpaddr0"]).a_uint64_t);
    this->put_csr(CSR_PMPCFG0, (this->params[base + "pmpcfg0"]).a_uint64_t);

    uint64_t max_misa = this->isa->get_max_isa();
    this->state.csrmap[CSR_MISA] = this->state.misa =
        std::make_shared<misa_csr_t>(this, CSR_MISA, max_misa);

    this->get_state()->csrmap[CSR_MSCONTEXT] = std::make_shared<proxy_csr_t>(this, CSR_MSCONTEXT, this->get_state()->csrmap[CSR_MCONTEXT]);

    this->get_state()->debug_mode = 1;

    for (auto it = Processor::csr_params.begin(); it != Processor::csr_params.end(); it++) {
        string csr_name = it->second.name;

        openhw::reg* p_csr = (openhw::reg*) this->state.csrmap[it->first].get();


        if (it->second.override_mask_param) {
            uint64_t override_mask = (this->params[base + csr_name + "_override_mask"]).a_uint64_t;
            uint64_t override_value = (this->params[base + csr_name + "_override_value"]).a_uint64_t;

            uint64_t val = p_csr->unlogged_read();
            val = (~override_mask & val) | (override_mask & override_value);
            // Write the value to the CSR
            p_csr->backdoor_write(val);
            // Affect possible dependencies
            p_csr->write(val);
        }

        if (it->second.presence_param) {
            bool presence = (this->params[base + csr_name + "_presence"]).a_bool;
            auto csr_it = state.csrmap.find(it->first);
            if (csr_it != state.csrmap.end() and !presence)
                state.csrmap.erase(csr_it);
        }

        if (it->second.write_enable_param) {
            bool we_enable = (this->params[base + csr_name + "_we_enable"]).a_bool;
            bool we = (this->params[base + csr_name + "_we"]).a_bool;
            if (we_enable)
                p_csr->set_we(we);
        }


    }

    this->get_state()->debug_mode = 0;

    bool fs_field_we_enable = (this->params[base + "status_fs_field_we_enable"]).a_bool;
    bool fs_field_we = (this->params[base + "status_fs_field_we"]).a_bool;
    bool vs_field_we_enable = (this->params[base + "status_vs_field_we_enable"]).a_bool;
    bool vs_field_we = (this->params[base + "status_vs_field_we"]).a_bool;
    bool xs_field_we_enable = (this->params[base + "status_xs_field_we_enable"]).a_bool;
    bool xs_field_we = (this->params[base + "status_xs_field_we"]).a_bool;

    reg_t sstatus_mask = this->state.csrmap[CSR_MSTATUS]->get_param_write_mask();
    if (fs_field_we_enable)
        sstatus_mask = (fs_field_we ? (sstatus_mask |  MSTATUS_FS)
                                    : (sstatus_mask & ~MSTATUS_FS));
    if (vs_field_we_enable)
        sstatus_mask = (vs_field_we ? (sstatus_mask |  MSTATUS_VS)
                                    : (sstatus_mask & ~MSTATUS_VS));

    if (xs_field_we_enable)
        sstatus_mask = (xs_field_we ? (sstatus_mask |  MSTATUS_XS)
                                    : (sstatus_mask & ~MSTATUS_XS));

    this->state.csrmap[CSR_MSTATUS]->set_param_write_mask(sstatus_mask);

    // Hide CSR Priv param implementation
    bool hide_csr_priv = (this->params[base + "hide_csr_priv"]).a_bool;
    std::string s = this->get_cfg().priv();
    if (hide_csr_priv) {
        for (auto it = this->get_state()->csrmap.begin(); it != this->get_state()->csrmap.end() ; it++) {
            bool legal = false;
            for (size_t i = 0 ; i < s.length() && !legal; i++) {
                std::tuple <uint64_t, uint64_t> range = Processor::priv_ranges[s[i]];
                if (std::get<0>(range) <= it->first && it->first < get<1>(range)) {
                    legal = true;
                }
            }
            if (!legal) {
                this->get_state()->csrmap.erase(it);
            }
        }
    }

}

void Processor::take_pending_interrupt() {
    uint64_t mie = (state.mie->read());
    uint64_t mip = (state.mip->read());
    take_interrupt(mip & mie);
}

void Processor::take_interrupt(reg_t pending_interrupts) {

  processor_t::take_interrupt(pending_interrupts);

  if (this->interrupt_injected && !this->taken_trap && pending_interrupts == 0) {
    uint64_t nmi_mcause = (this->params[base + "nmi_mcause"]).a_uint64_t;
    throw trap_t(((reg_t)1 << (isa->get_max_xlen() - 1)) | nmi_mcause);
  }
  return;
}

uint32_t Processor::mcause_to_mip(uint32_t mcause) {
    // Check if the cause is an interrupt (MSB = 1)
    if (mcause >> 31) {
        uint32_t interrupt_id = mcause & 0x7FFFFFFF; // Mask out the interrupt bit to get the ID
        switch (interrupt_id) {
            case 3: return MIP_MSIP;   // Software interrupt
            case 7: return MIP_MTIP;   // Timer interrupt
            case 11: return MIP_MEIP;  // External interrupt
            default:
                if (32 > interrupt_id && interrupt_id > 15) {
                    return 1 << (interrupt_id);
                }
                return 0;         // Unknown or unhandled interrupt
        }
    }
    return 0; // Not an interrupt
}

std::unordered_map<uint64_t, openhw::csr_param_t> Processor::csr_params = {
    // ADDRESS          NAME      OVERRIDE_MASKS_PARAM   PRESENCE_PARAM  WRITE_ENABLE_PARAM
    { CSR_MSTATUS   , {"mstatus"    ,  true    ,           false       ,      true} },
    { CSR_MISA      , {"misa"       ,  true    ,           false       ,      true} },
    { CSR_MHARTID   , {"mhartid"    ,  true    ,           false       ,      true} },
    { CSR_MARCHID   , {"marchid"    ,  true    ,           false       ,      true} },
    { CSR_MVENDORID , {"mvendorid"  ,  true    ,           false       ,      true} },
    { CSR_TDATA1    , {"tdata1"     ,  true    ,           false       ,      true} },
    { CSR_TINFO     , {"tinfo"      ,  true    ,           true        ,      true} },
    { CSR_MSCONTEXT , {"mscontext"  ,  true    ,           true        ,      true} },
  };

std::unordered_map<char, std::tuple<uint64_t,uint64_t>> Processor::priv_ranges = {
    { 'M',  {0x300, 0xFFF} },
    { 'S',  {0x100, 0x200} },
    { 'U',  {0x0  , 0x100} },
};

} // namespace openhw
