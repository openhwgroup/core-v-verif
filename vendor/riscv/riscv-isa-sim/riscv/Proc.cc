#include "Proc.h"
#include "disasm.h"
#include "extension.h"
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
st_rvfi Processor::step(size_t n, st_rvfi reference) {
  st_rvfi rvfi;
  memset(&rvfi, 0, sizeof(st_rvfi));

  this->taken_trap = false;
  this->which_trap = 0;

  rvfi.pc_rdata = this->get_state()->pc;
  processor_t::step(n);

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

  rvfi.trap = this->taken_trap;
  rvfi.trap |= (this->which_trap << 1);

  bool got_commit = false;
  for (auto &reg : reg_commits) {
      if ((reg.first >> 4) > 32) {
          if ((reg.first >> 4) < 0xFFF) {
            for (size_t i = 0; i < CSR_SIZE; i++) {
                if (!rvfi.csr_valid[i]) {
                    rvfi.csr_valid[i] = 1;
                    rvfi.csr_addr[i] = reg.first >> 4;
                    rvfi.csr_wdata[i] = reg.second.v[0];
                    rvfi.csr_wmask[i] = -1;
                    break;
                }
            }
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

  // Inject values comming from the reference
  if ((rvfi.insn & MASK_CSRRS) == MATCH_CSRRS) {
    if (rvfi.rs1_addr == 0) {
      reg_t read_csr = this->get_state()->last_inst_fetched.csr();
      switch (read_csr) {
      case 0xC00: // cycle
      case 0xC80: // cycleh
      case 0xB00: // mcycle
      case 0xB80: // mcycleh
        this->set_XPR(reference.rd1_addr, reference.rd1_wdata);
        rvfi.rd1_wdata = reference.rd1_wdata;
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
  return rvfi;
}

Processor::Processor(
    const isa_parser_t *isa, const cfg_t *cfg, simif_t *sim, uint32_t id,
    bool halt_on_reset, FILE *log_file, std::ostream &sout_,
    Params &params) // because of command line option --log and -s we need both
    : processor_t::processor_t(isa, cfg, sim, id, halt_on_reset, log_file,
                               sout_) {

  std::map<string, bool> registered_extensions_v;
  registered_extensions_v["cv32a60x"] = false;

  string base = "/top/core/" + std::to_string(id) + "/";
  Processor::default_params(base, this->params);
  Params::parse_params(base, this->params, params);

  string isa_str = std::any_cast<string>(this->params[base + "isa"]);
  string priv_str = std::any_cast<string>(this->params[base + "priv"]);
  std::cout << "[SPIKE] Proc 0 | ISA: " << isa_str << " PRIV: " << priv_str << std::endl;
  this->isa =
      (const isa_parser_t *)new isa_parser_t(isa_str.c_str(), priv_str.c_str());

  disassembler = new disassembler_t(isa);

  for (auto e : isa->get_extensions()) {
    register_extension(e.second);
  }

  this->n_pmp = std::any_cast<uint64_t>(this->params[base + "pmpregions"]);

  ((cfg_t *)cfg)->misaligned =
      std::any_cast<bool>(this->params[base + "misaligned"]);

  string extensions_str =
      std::any_cast<string>(this->params[base + "extensions"]);
  string delimiter = ",";
  size_t found = extensions_str.rfind(delimiter);

  if (found == string::npos && extensions_str != "") {
    extensions_str = extensions_str + delimiter;
  }

  while (found != string::npos) {
    string token = extensions_str.substr(found + delimiter.length(),
                                         extensions_str.length() - 1);
    extensions_str = extensions_str.substr(0, found);
    auto it = registered_extensions_v.find(token);
    if (it != registered_extensions_v.end())
      it->second = true;
    else
      std::cout << "[SPIKE] Extension \"" << token << "\" can not be registered"
                << std::endl;

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

  uint64_t new_pc = std::any_cast<uint64_t>(this->params[base + "boot_addr"]);
  this->state.pc = new_pc;

  this->put_csr(CSR_PMPADDR0,
                std::any_cast<uint64_t>(this->params[base + "pmpaddr0"]));
  this->put_csr(CSR_PMPCFG0,
                std::any_cast<uint64_t>(this->params[base + "pmpcfg0"]));

  this->state.csrmap[CSR_MVENDORID] =
      std::make_shared<const_csr_t>(this, CSR_MVENDORID, std::any_cast<uint64_t>(this->params[base + "mvendorid"]));
  this->state.csrmap[CSR_MHARTID] =
      std::make_shared<const_csr_t>(this, CSR_MHARTID, std::any_cast<uint64_t>(this->params[base + "mhartid"]));
  this->state.csrmap[CSR_MARCHID] =
      std::make_shared<const_csr_t>(this, CSR_MHARTID, std::any_cast<uint64_t>(this->params[base + "marchid"]));

  bool fs_field_we_enable =
      std::any_cast<bool>(this->params[base + "status_fs_field_we_enable"]);
  bool fs_field_we =
      std::any_cast<bool>(this->params[base + "status_fs_field_we"]);
  bool vs_field_we_enable =
      std::any_cast<bool>(this->params[base + "status_vs_field_we_enable"]);
  bool vs_field_we =
      std::any_cast<bool>(this->params[base + "status_vs_field_we"]);

  reg_t sstatus_mask = this->state.mstatus->get_param_write_mask();
  if (fs_field_we_enable)
    sstatus_mask = (fs_field_we ? (sstatus_mask | MSTATUS_FS)
                                : (sstatus_mask & ~MSTATUS_FS));
  if (vs_field_we_enable)
    sstatus_mask = (vs_field_we ? (sstatus_mask | MSTATUS_VS)
                                : (sstatus_mask & ~MSTATUS_VS));
  this->state.mstatus->set_param_write_mask(sstatus_mask);

  bool misa_we_enable =
      std::any_cast<bool>(this->params[base + "misa_we_enable"]);
  bool misa_we = std::any_cast<bool>(this->params[base + "misa_we"]);
  if (misa_we_enable)
    this->state.misa->set_we(misa_we);
}

void Processor::take_trap(trap_t &t, reg_t epc) {
  this->taken_trap = true;
  this->which_trap = t.cause();
  processor_t::take_trap(t, epc);
}

Processor::~Processor() { delete this->isa; }

void Processor::default_params(string base, openhw::Params &params) {
  params.set(base, "isa", any(std::string("RV32GC")), "string", "RV32GC",
             "ISA");
  params.set(base, "priv", any(std::string(DEFAULT_PRIV)), "string",
             DEFAULT_PRIV, "Privilege Level");
  params.set(base, "boot_addr", any(0x80000000UL), "uint64_t", "0x80000000UL",
             "First PC of the core");
  params.set(base, "mmu_mode", any(std::string("sv39")), "string", "sv39",
             "Memory virtualization mode");

  params.set(base, "pmpregions", std::any(0x0UL), "uint64_t", "0x0",
             "Number of PMP regions");
  params.set(base, "pmpaddr0", any(0x0UL), "uint64_t", "0x0",
             "Default PMPADDR0 value");
  params.set(base, "pmpcfg0", any(0x0UL), "uint64_t", "0x0",
             "Default PMPCFG0 value");
  params.set(base, "marchid", any(0x3UL), "uint64_t", "0x3", "MARCHID value");
  params.set(base, "mhartid", any(0x0UL), "uint64_t", "0x0", "MHARTID value");
  params.set(base, "mvendorid", any(0x00000602UL), "uint64_t", "0x00000602UL",
             "MVENDORID value");
  params.set(base, "extensions", any(std::string("")), "string",
             "\"extension1,extension2\"", "Possible extensions: cv32a60x");

  params.set(base, "status_fs_field_we_enable", any(false), "bool", "false",
             "XSTATUS CSR FS Write Enable param enable");
  params.set(base, "status_fs_field_we", any(false), "bool", "false",
             "XSTATUS CSR FS Write Enable");
  params.set(base, "status_vs_field_we_enable", any(false), "bool", "false",
             "XSTATUS CSR VS Write Enable param enable");
  params.set(base, "status_vs_field_we", any(false), "bool", "false",
             "XSTATUS CSR VS Write Enable");
  params.set(base, "misa_we_enable", any(true), "bool", "true",
             "MISA CSR Write Enable param enable");
  params.set(base, "misa_we", any(false), "bool", "false",
             "MISA CSR Write Enable value");

  params.set(base, "misaligned", std::any(false), "bool", "false",
             "Support for misaligned memory operations");
}

inline void Processor::set_XPR(reg_t num, reg_t value) {
  this->state.XPR.write(num, value);
}

inline void Processor::set_FPR(reg_t num, float128_t value) {
  this->state.FPR.write(num, value);
}

} // namespace openhw
