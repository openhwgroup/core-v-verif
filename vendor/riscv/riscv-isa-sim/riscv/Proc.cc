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
  this->step_rvfi = & rvfi;

  bool unified_traps = (this->params[base + "unified_traps"]).a_bool;
  bool interrupts_injection = (this->params[base + "interrupts_injection"]).a_bool;
  bool debug_injection = (this->params[base + "debug_injection"]).a_bool;
  // Use mstatus as a reference
  bool inverse_csr_access = (reference->csr_addr[0x300] != 0x300);

#define INDEX_CSR(INDEX) (inverse_csr_access) ? CSR_MAX_SIZE-1-INDEX : INDEX

  memset(&rvfi, 0, sizeof(st_rvfi));

  do {

    if (this->is_waiting_for_interrupt())
        this->clear_waiting_for_interrupt();

    bool inject_interrupt = ((this->reference->intr & 0b111) == 0b101);

    if (inject_interrupt && interrupts_injection && !this->taken_trap) {
        // We need to ensure this is an interrupt to inject mip
        uint64_t mcause = reference->csr_rdata[INDEX_CSR(CSR_MCAUSE)];
        if (mcause >> 31) {
            uint64_t mip = this->mcause_to_mip(mcause);
            this->get_state()->mip->backdoor_write(mip);
            this->step_rvfi->intr = 0b101; // Interrupt
            this->step_rvfi->intr |= ((mcause & 0x3FF) << 3);
            uint64_t nmi_mcause = (this->params[base + "nmi_mcause"]).a_uint64_t;
            if (nmi_mcause == (mcause & 0x3FF))
                this->nmi_inject = true;
        }
    }

    if (reference->dbg && !this->get_state()->debug_mode && debug_injection && !this->halted()) {
        uint64_t cause = reference->dbg;
        if (cause) {
            enter_debug_mode(cause);
            rvfi.dbg = cause;
            rvfi.trap = 0b101;
            rvfi.trap |= (cause << 9);
        }
    }

    if (this->taken_trap && !(this->which_trap >> 31)) {
        rvfi.intr = 0b011;
    }

    if (this->taken_debug) {
        rvfi.dbg = this->which_debug;
    }

    this->taken_trap = false;
    this->which_trap = 0;
    this->taken_debug = false;
    this->which_debug = 0;

    rvfi.pc_rdata = this->get_state()->pc;

    processor_t::step(n);

    if (this->taken_trap && (this->which_trap >> 31))
        this->get_state()->mip->backdoor_write(0);

    // First intr of the trap handler
    if ((this->taken_trap || this->taken_debug) && !(this->which_trap >> 31)) {
        rvfi.trap = 1;
        if (this->get_state()->debug_mode) {
            rvfi.trap |= 0x4;
            rvfi.trap |= (this->which_debug & 0x7) << 0x9;
        } else if (this->which_trap >> 31) {
            rvfi.trap |= 0x2;
            rvfi.trap |= (this->which_trap & 0x3F) << 0x3;
        }
    }

    rvfi.dbg_mode = this->get_state()->debug_mode;

    rvfi.mode = this->get_state()->last_inst_priv;
    rvfi.insn =
        (uint32_t)(this->get_state()->last_inst_fetched.bits() & 0xffffffffULL);

    // TODO FIXME Handle multiple/zero writes in a single insn.
    auto &reg_commits = this->get_state()->log_reg_write;
    int xlen = this->get_state()->last_inst_xlen;
    int flen = this->get_state()->last_inst_flen;

    rvfi.rs1_addr = this->get_state()->last_inst_fetched.rs1();
    rvfi.rs1_rdata = this->get_XPR(reference->rs1_addr);
    rvfi.rs2_addr = this->get_state()->last_inst_fetched.rs2();
    rvfi.rs2_rdata = this->get_XPR(reference->rs2_addr);

    bool got_commit = false;

    if (rvfi.intr) {
        for (auto &reg : last_log_reg_write) {
            reg_t addr = reg.first >> 4;
            rvfi.csr_valid[INDEX_CSR(addr)] = 1;
            rvfi.csr_addr [INDEX_CSR(addr)] = addr;
            rvfi.csr_wdata[INDEX_CSR(addr)] = reg.second.v[0];
            rvfi.csr_wmask[INDEX_CSR(addr)] = -1;
        }
    }
    last_log_reg_write.clear();

    for (auto &reg : reg_commits) {
        if ((reg.first >> 4) > 32) {
            if (rvfi.trap) {
                last_log_reg_write[reg.first] = reg.second;
            }
            else if ((reg.first >> 4) < 0xFFF) {
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

    if (csr_counters_injection & !rvfi.trap) {
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
              this->set_XPR(reference->rd1_addr, this->xlen_format(reference->rd1_wdata));
              rvfi.rd1_wdata = reference->rd1_wdata;
            }

            // If it is set or clear we need to inject also the value in the CSR
            if (this->get_state()->last_inst_fetched.rs1()) {
                if ((rvfi.insn & MASK_CSRRC) == MATCH_CSRRC   ||
                    (rvfi.insn & MASK_CSRRS) == MATCH_CSRRS   ||
                    (rvfi.insn & MASK_CSRRCI) == MATCH_CSRRCI ||
                    (rvfi.insn & MASK_CSRRSI) == MATCH_CSRRSI) {

                    if (reference->csr_valid[INDEX_CSR(read_csr)]) {
                        this->put_csr(read_csr, this->xlen_format(reference->csr_wdata[INDEX_CSR(read_csr)]));
                        rvfi.csr_wdata[INDEX_CSR(read_csr)] = reference->csr_wdata[INDEX_CSR(read_csr)];
                    }
                }
            }
            if ((rvfi.insn & MASK_CSRRW) == MATCH_CSRRW   ||
                (rvfi.insn & MASK_CSRRWI) == MATCH_CSRRWI) {

                if (reference->csr_valid[INDEX_CSR(read_csr)]) {
                    this->put_csr(read_csr, this->xlen_format(reference->csr_wdata[INDEX_CSR(read_csr)]));
                    rvfi.csr_wdata[INDEX_CSR(read_csr)] = reference->csr_wdata[INDEX_CSR(read_csr)];
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

  } while (unified_traps && this->taken_trap && (this->which_trap >> 31));

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
  Processor::default_params(base, this->params, this);
  Params::parse_params(base, this->params, params_);

  string isa_str = this->params[base + "isa"].a_string;
  string priv_str = this->params[base + "priv"].a_string;
  this->isa =
      (const isa_parser_t *)new isa_parser_t(isa_str.c_str(), priv_str.c_str());
  std::cout << "[SPIKE] Proc 0 | ISA: " << isa_str << " PRIV: " << priv_str << std::endl;
  std::cout << "[SPIKE]     Non standard interrupts " << this->params[base + "non_standard_interrupts"].a_bool << std::endl;

  uint64_t pmpregions_max = this->params[base + "pmpregions_max"].a_uint64_t;
  std::cout << "[SPIKE]                 PMP Regions " << std::hex << pmpregions_max << std::endl;
  processor_t::set_pmp_num(pmpregions_max);

  uint64_t pmp_granularity = this->params[base + "pmp_granularity"].a_uint64_t;
  std::cout << "[SPIKE]                 PMP Granularity " << pmp_granularity;
  // PMP granularity must be at least 4 and a power of two.
  if (pmp_granularity < 4 || (pmp_granularity & (pmp_granularity - 1)) != 0)
    std::cout << " is INVALID, will be IGNORED." << std::endl;
  else {
    std::cout << std::endl;
    processor_t::set_pmp_granularity(pmp_granularity);
  }

  ((cfg_t *)cfg)->priv = priv_str.c_str();

  uint64_t trigger_count = this->params[base + "trigger_count"].a_uint64_t;
  ((cfg_t *)cfg)->trigger_count = trigger_count;

  if (disassembler != NULL)
      delete disassembler;

  this->disassembler = new disassembler_t(this->isa);

  for (auto e : this->isa->get_extensions()) {
    register_extension(e.second);
  }

  this->taken_trap = false;
  this->taken_debug = false;
  this->nmi_inject = false;


  ((cfg_t *)cfg)->misaligned =
      (this->params[base + "misaligned"]).a_bool;

  this->csr_counters_injection =
      (this->params[base + "csr_counters_injection"]).a_bool;
  string extensions_str =
      (this->params[base + "extensions"]).a_string;

  string delimiter = ",";

  extensions_str = extensions_str + delimiter;

  size_t found = extensions_str.find(delimiter);

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

  if (state.debug_mode) {
    uint64_t debug_handler_addr = (this->params[base + "debug_handler_addr"]).a_uint64_t;
    uint64_t debug_exception_handler_addr = (this->params[base + "debug_exception_handler_addr"]).a_uint64_t;
    if (this->which_trap == 0x3) {
        state.pc = debug_handler_addr;
        this->which_trap = 0x1; // Debug breakpoint on debug mode
    }
    else
        state.pc = debug_exception_handler_addr;
  }
}

Processor::~Processor() {
    delete this->isa;
    for (auto e : this->custom_extensions)
        delete e.second;
}

void Processor::default_params(string base, openhw::Params &params, Processor *proc) {
  params.set_string(base, "isa", "RV32GC", "RV32GC",
             "ISA");
  params.set_string(base, "priv", DEFAULT_PRIV, DEFAULT_PRIV, "Privilege Level");
  params.set_uint64_t(base, "boot_addr", 0x80000000UL, "0x80000000UL",
             "First PC of the core");
  params.set_string(base, "mmu_mode", "sv39", "sv39",
             "Memory virtualization mode");

  if (!params.exist(base, "pmpregions_max"))
    params.set_uint64_t(base, "pmpregions_max", 0x0UL, "0x0",
                        "Number of PMP regions");
  if (!params.exist(base, "pmpregions_writable"))
    params.set_uint64_t(base, "pmpregions_writable", 0x0UL, "0x0",
                        "Number of PMP regions");
  if (!params.exist(base, "pmp_granularity"))
    params.set_uint64_t(base, "pmp_granularity", 0x8UL, "0x8",
                        "Granularity of PMP addresses in bytes");
  if (!params.exist(base, "pmpaddr0"))
    params.set_uint64_t(base, "pmpaddr0", 0x0UL, "0x0",
			"Default PMPADDR0 value");
  if (!params.exist(base, "pmpcfg0"))
    params.set_uint64_t(base, "pmpcfg0", 0x0UL, "0x0",
			"Default PMPCFG0 value");
  if (!params.exist(base, "marchid"))
    params.set_uint64_t(base, "marchid", 0x3UL, "0x3", "MARCHID value");
  if (!params.exist(base, "mhartid"))
    params.set_uint64_t(base, "mhartid", 0x0UL, "0x0", "MHARTID value");
  if (!params.exist(base, "mvendorid"))
    params.set_uint64_t(base, "mvendorid", 0x00000602UL, "0x00000602UL",
			"MVENDORID value");

  if (!params.exist(base, "debug_handler_addr"))
    params.set_uint64_t(base, "debug_handler_addr", 0x1a110800, "0x1a110800",
			"Debug handler Address");

  if (!params.exist(base, "debug_exception_handler_addr"))
    params.set_uint64_t(base, "debug_exception_handler_addr", 0x1A140000, "0x1A140000",
			"Debug handler Address");

  if (!params.exist(base, "extensions"))
    params.set_string(base, "extensions", "", "", "Possible extensions: cv32a60x, cvxif");

  if (!params.exist(base, "misaligned"))
    params.set_bool(base, "misaligned", false, "false",
		    "Support for misaligned memory operations");

  if (!params.exist(base, "csr_counters_injection"))
    params.set_bool(base, "csr_counters_injection", false, "false",
		    "Allow to set CSRs getting values from DPI");

  if (!params.exist(base, "interrupts_injection"))
    params.set_bool(base, "interrupts_injection", true, "true",
		    "Allow to set MIP csr with values from DPI");

  if (!params.exist(base, "debug_injection"))
    params.set_bool(base, "debug_injection", true, "true",
		    "Allow to enter in debug mode with values from DPI");

  if (!params.exist(base, "hide_csrs_based_on_priv"))
    params.set_bool(base, "hide_csrs_based_on_priv", false, "false",
		    "Allow to hide CSRs based on priv modes available.");

  if (!params.exist(base, "mtvec_vectored_alignment"))
    params.set_uint64_t(base, "mtvec_vectored_alignment", 0x4UL, "0x4",
			"Default alignment for mtvec when vector mode active");

  if (!params.exist(base, "override_custom_extensions"))
    params.set_bool(base, "override_custom_extensions", true, "false",
		    "Allow to override custom extensions value.");

  if (!params.exist(base, "override_custom_extensions_value"))
    params.set_bool(base, "override_custom_extensions_value", false, "false",
		    "Value for the custom extensions override.");

 if (!params.exist(base, "non_standard_interrupts"))
     params.set_bool(base, "non_standard_interrupts", false, "false",
		     "Value for the custom extensions override.");

  if (!params.exist(base, "unified_traps"))
    params.set_bool(base, "unified_traps", false, "false",
		    "Unify all kind of traps with the exceptions.");

  if (!params.exist(base, "nmi_mcause"))
    params.set_uint64_t(base, "nmi_mcause", 0x00000020, "0x00000020",
			"Value of MCAUSE in case of NMI. It does not include the interrupt bit.");

  for (auto it = proc->get_state()->csrmap.begin(); it != proc->get_state()->csrmap.end(); it++) {
      string csr_name = it->second.get()->get_name();
      if (csr_name != "noname") {
        params.set_uint64_t(base, csr_name + "_override_value", (0x0UL), "0x0",
                    csr_name + " CSR override value");
        params.set_uint64_t(base, csr_name + "_override_mask", (0x0UL), "0x0",
                    csr_name + " CSR override mask");
        params.set_bool(base, csr_name + "_accessible", true, "true",
                    csr_name + " CSR accessible");
        params.set_bool(base, csr_name + "_implemented", true, "true",
                    csr_name + " CSR implemented");
        params.set_bool(base, csr_name + "_we_enable", false, "false",
                    csr_name +" CSR Write Enable param enable");
        params.set_bool(base, csr_name + "_we", false, "false",
                    csr_name + " CSR Write Enable value");
        params.set_uint64_t(base, csr_name + "_write_mask", ((uint64_t) -1ULL), "0xFFFFFFFF",
                        csr_name + " CSR write mask");
      }
  }

  if (!params.exist(base, "trigger_count"))
    params.set_uint64_t(base, "trigger_count", 0x0000004, "0x00000004",
			"Number of enabled triggers");
}

inline uint64_t Processor::get_XPR(reg_t num) {
  return this->state.XPR[num];
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

reg_t Processor::get_csr(int which)
{
    return this->get_csr(which, 0, 0, 1);
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

    auto it = this->get_state()->csrmap.begin();
    while (it != this->get_state()->csrmap.end()) {

        openhw::reg* p_csr = (openhw::reg*) it->second.get();
        std::string csr_name = reg::addr2name(it->first);
        if (csr_name != "") {
            p_csr->set_name(csr_name);

            uint64_t override_mask = (this->params[base + csr_name + "_override_mask"]).a_uint64_t;
            uint64_t override_value = (this->params[base + csr_name + "_override_value"]).a_uint64_t;

            uint64_t val = p_csr->unlogged_read();
            val = (~override_mask & val) | (override_mask & override_value);
            // Write the value to the CSR
            p_csr->backdoor_write(val);
            // Affect possible dependencies
            if (val != p_csr->read())
                p_csr->write(val);

            string write_mask_string = base + csr_name + "_write_mask";
            uint64_t write_mask = (this->params[base + csr_name + "_write_mask"]).a_uint64_t;
            p_csr->set_param_write_mask(write_mask);

            bool implemented = (this->params[base + csr_name + "_implemented"]).a_bool;
            p_csr->set_param_implemented(implemented);
            if (!implemented) {
                p_csr->set_param_write_mask(0x0);
                p_csr->backdoor_write(0x0);
                if (p_csr->read())
                    p_csr->write(0);
            }

            bool accessible = (this->params[base + csr_name + "_accessible"]).a_bool;
            p_csr->set_param_accessible(accessible);
            if (!accessible)
                state.csrmap.erase(it++);
            else
                it++;

        }
        else
            it++;
    }

    this->get_state()->debug_mode = 0;

    // Hide CSR Priv param implementation
    bool hide_csr_priv = (this->params[base + "hide_csrs_based_on_priv"]).a_bool;
    std::string s = this->get_cfg().priv();
    if (hide_csr_priv) {
        auto it = this->get_state()->csrmap.begin();
        while(it != this->get_state()->csrmap.end()) {
            bool legal = false;
            for (size_t i = 0 ; i < s.length() && !legal; i++) {
                std::tuple <uint64_t, uint64_t> range = Processor::priv_ranges[s[i]];
                if (std::get<0>(range) <= it->first && it->first < get<1>(range)) {
                    legal = true;
                }
            }
            if (!legal)
                this->get_state()->csrmap.erase(it++);
            else
                it++;
        }
    }

    uint64_t pmpregions_writable = this->params[base + "pmpregions_writable"].a_uint64_t;
    uint64_t pmpregions_max = this->params[base + "pmpregions_max"].a_uint64_t;

    for (int i = pmpregions_writable; i < pmpregions_max; i++) {
        uint64_t csr_pmpaddr = CSR_PMPADDR0 + i;
        uint64_t csr_pmpcfg = CSR_PMPCFG0 + (i/4);

        auto addr_it = this->get_state()->csrmap.find(csr_pmpaddr);
        if (addr_it != this->get_state()->csrmap.end()) {
            openhw::reg* p_csr = (openhw::reg*) addr_it->second.get();
            p_csr->set_param_write_mask(0x0);
            p_csr->set_param_implemented(0x0);

        }
        auto cfg_it = this->get_state()->csrmap.find(csr_pmpcfg);
        if (cfg_it != this->get_state()->csrmap.end()) {
            openhw::reg* p_csr = (openhw::reg*) cfg_it->second.get();
            p_csr->set_param_implemented(0x0);
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

  if (this->nmi_inject && !this->taken_trap && pending_interrupts == 0) {
    this->nmi_inject = false;
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

void Processor::enter_debug_mode(uint8_t cause) {
    processor_t::enter_debug_mode(cause);

    uint64_t debug_handler_addr = (this->params[base + "debug_handler_addr"]).a_uint64_t;
    state.pc = debug_handler_addr;
    state.mtval->write(0x0);

    this->taken_debug = true;
    this->which_debug = cause;

}

uint64_t Processor::xlen_format(uint64_t value) {
    if (this->get_xlen() == 32) {
        return sreg_t((int32_t) value);
    } else {
        return value;
    }
}

std::unordered_map<char, std::tuple<uint64_t,uint64_t>> Processor::priv_ranges = {
    { 'M',  {0x300, 0xFFF} },
    { 'S',  {0x100, 0x200} },
    { 'U',  {0x0  , 0x100} },
};

} // namespace openhw
