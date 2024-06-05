#include "Proc.h"
#include "disasm.h"
#include "extension.h"
#include "mmu.h"
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
  commit_log_reg_t prev_commit_log_reg = this->get_state()->log_reg_write;


  this->taken_trap = false;
  this->which_trap = 0;

  // Store the state before stepping
  state_t prev_state = *this->get_state();

  // Disable WFI to handle the timing outside of spike.
  in_wfi = false;
  processor_t::step(n);

  rvfi.pc_rdata = this->last_pc;

  // Add overwritten values from memory writes during the step
  prev_changes_t prev_changes(prev_state, this->get_state()->log_mem_pre_write);
  if(max_previous_states > 0) {
    previous_states.push_front(prev_changes);
  }
  if(previous_states.size() > max_previous_states) {
    previous_states.pop_back();
  }

  rvfi.pc_wdata = this->get_state()->pc; // Next predicted PC

  rvfi.mode = this->get_state()->last_inst_priv;
  rvfi.insn =
      (uint32_t)(this->get_state()->last_inst_fetched.bits() & 0xffffffffULL);

  // TODO FIXME Handle multiple/zero writes in a single insn.
  auto &reg_commits = this->get_state()->log_reg_write;
  auto &mem_write_commits = this->get_state()->log_mem_write;
  auto &mem_read_commits = this->get_state()->log_mem_read;
  int xlen = this->get_state()->last_inst_xlen;
  int flen = this->get_state()->last_inst_flen;

  rvfi.rs1_addr = this->get_state()->last_inst_fetched.rs1();
  // TODO add rs1_value
  rvfi.rs2_addr = this->get_state()->last_inst_fetched.rs2();
  // TODO add rs2_value


  if(this->next_rvfi_intr){
    rvfi.intr = next_rvfi_intr;
    this->next_rvfi_intr = 0;

    //Add csr changes that happened during first interrupt step
    reg_commits.insert(prev_commit_log_reg.begin(), prev_commit_log_reg.end());
  }
  
  // Output dbg caused from EBREAK the previous instruction
  if(this->next_debug) {
    rvfi.dbg = this->next_debug;
    this->next_debug = 0;
  }

  if(this->state.debug_mode  && (prev_state.debug_mode == 0)){
    // New external debug request
    if((this->halt_request != HR_NONE)){ 
      rvfi.dbg = this->get_state()->dcsr->cause;
      rvfi.dbg_mode = 1;

    // EBREAK
    } else if(this->get_state()->dcsr->cause == DCSR_CAUSE_SWBP) {
      // EBREAK will set debug_mode to 1, but we should report this at the next instruction
      rvfi.trap |= 1 << 0; //trap [0]
      rvfi.trap |= 1 << 2; //debug [2]
      rvfi.trap |= 0xE00 & ((DCSR_CAUSE_SWBP) << 9); //debug cause [11:9]
      
      this->next_debug = DCSR_CAUSE_SWBP;
    }
  }

  // Set dbg_mode to 1 the first instruction in debug mode, but delay turning 
  // off dbg_mode to the next instruction after turning off to keep dbg_mode on for dret
  if( (this->halt_request != HR_NONE)  && (prev_state.debug_mode == 0)) {
    rvfi.dbg_mode = 1;
  } else {
    rvfi.dbg_mode = prev_state.debug_mode;
  }


  if(this->taken_trap) {
    //interrrupts are marked with the msb high in which_trap
    if(this->which_trap & ((reg_t)1 << (isa->get_max_xlen() - 1))) { 
      //Since spike steps two times to take an interrupt, we store the intr value to the next step to return with rvfi
      this->next_rvfi_intr |= 1 << 0; //intr [0]
      this->next_rvfi_intr |= 1 << 2; //interrupt [2]
      this->next_rvfi_intr |= 0x3FF8 & ((this->which_trap & 0xFF) << 3); //cause[13:3]
    } else{
      rvfi.trap |= 1 << 0; //trap [0]
      rvfi.trap |= 1 << 1; //exception [1]
      rvfi.trap |= 0x1F8 & ((this->which_trap) << 3); //exception_cause [8:3]
      //TODO:
      //debug_cause     [11:9] debug cause
      //cause_type      [13:12]
      //clicptr         [14]  CLIC interrupt pending
      this->next_rvfi_intr = rvfi.trap; //store value to return with rvfi.intr on the next step
    }
  }

  uint64_t last_rd_addr = 0;
  uint64_t last_rd_wdata = 0;
  bool got_commit = false;
  for (auto &reg : reg_commits) {
    if((reg.first & 0xf) == 0x4) { //If CSR
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
    else {
      if (got_commit) {
        last_rd_addr = reg.first >> 4;
        last_rd_wdata = reg.second.v[0];
        continue;
      }
      // TODO FIXME Take into account the XLEN/FLEN for int/FP values.
      rvfi.rd1_addr = reg.first >> 4;
      rvfi.rd1_wdata = reg.second.v[0];
      // TODO FIXME Handle multiple register commits per cycle.
      // TODO FIXME This must be handled on the RVFI side as well.
      got_commit = true; // Only latch first commit
    }
  }
  // popret(z) should return rd1_addr = 0 instead of the SP to match with the cv32e40s core
  if (((this->get_state()->last_inst_fetched.bits() & MASK_CM_POPRET) == MATCH_CM_POPRET) ||
      ((this->get_state()->last_inst_fetched.bits() & MASK_CM_POPRETZ) == MATCH_CM_POPRETZ)) {
    rvfi.rd1_addr = 0;
    rvfi.rd1_wdata = 0;
  }

  bool mem_access = false; // TODO: support multiple memory writes/reads
  int read_len;
  for (auto &mem : mem_read_commits) {
    //mem format: (addr, 0, size) (value is not stored for reads, but should be the same as rd)
    if(!mem_access) {
      rvfi.mem_addr = std::get<0>(mem);
      if ((this->get_state()->last_inst_fetched.bits() & MASK_CM_POP) == MATCH_CM_POP         ||
          (this->get_state()->last_inst_fetched.bits() & MASK_CM_POPRET) == MATCH_CM_POPRET   ||
          (this->get_state()->last_inst_fetched.bits() & MASK_CM_POPRETZ) == MATCH_CM_POPRETZ ){    
        rvfi.mem_rdata = last_rd_wdata; // During pop, rd1 returns sp, so instead return value read from memory 
      } else {
        rvfi.mem_rdata = rvfi.rd1_wdata; 
      }
      //mem_rmask should hold a bitmask of which bytes in mem_rdata contain valid data
      read_len = std::get<2>(mem);
      rvfi.mem_rmask = (1 << read_len) - 1;
      mem_access = true;
    }
  }

  int write_len;
  for (auto &mem : mem_write_commits) {
    //mem format: (addr, value, size)
    if(!mem_access) {
      rvfi.mem_addr = std::get<0>(mem);
      rvfi.mem_wdata = std::get<1>(mem); // value
      //mem_wmask should hold a bitmask of which bytes in mem_wdata contain valid data
      write_len = std::get<2>(mem);
      rvfi.mem_wmask = (1 << write_len) - 1;
      mem_access = true;
    }

  }
  
  if (csr_counters_injection) {
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
  }

  // Remove sign extension applied by Spike in 32b mode.
  if (this->get_xlen() == 32) {
    rvfi.pc_rdata &= 0xffffffffULL;
    rvfi.rd1_wdata &= 0xffffffffULL;
  }
  return rvfi;
}

void Processor::revert_step(uint32_t num_steps) {
  FILE *log_file = this->get_log_file();


  if (previous_states.size() < num_steps) {
    throw std::runtime_error("Cannot revert more states than stored");
  }

  for(auto state: previous_states) {
    fprintf(log_file, "pc: %lx | ", std::get<0>(state).pc);
  }
  fprintf(log_file, "\n");



  fprintf(log_file, "revert %d steps from PC: %lx", num_steps, this->state.pc);

  prev_changes_t prev_changes = previous_states[num_steps];
  this->state = std::get<0>(prev_changes);

  fprintf(log_file, " to PC: %lx\n", this->state.pc);

  for (uint32_t i = 0; i <= num_steps; i++) {
    prev_changes_t prev_changes = previous_states.front();
    previous_states.pop_front();

    commit_log_mem_t log_mem_pre_write = std::get<1>(prev_changes);
    fprintf(log_file, "revert mem pc: %lx num: %ld\n", std::get<0>(prev_changes).pc, log_mem_pre_write.size());

    for (auto mem_write : log_mem_pre_write) {
      fprintf(log_file, "revert mem: addr: %lx val: %lx size: %x", std::get<0>(mem_write), std::get<1>(mem_write), std::get<2>(mem_write));
      switch (std::get<2>(mem_write))
      {
      case 1:
        this->get_mmu()->store<uint8_t>(std::get<0>(mem_write), (uint8_t)std::get<1>(mem_write),0);
        break;
      case 2:
        this->get_mmu()->store<uint16_t>(std::get<0>(mem_write), (uint16_t)std::get<1>(mem_write),0);
        break;
      case 4:
        this->get_mmu()->store<uint32_t>(std::get<0>(mem_write), (uint32_t)std::get<1>(mem_write),0);
        break;
      
      default:
        break;
      }
      fprintf(log_file, " OK\n");
    }
  }

  //Clear commit logs since they contain information from the reverted steps
  this->get_state()->log_mem_write.clear();
  this->get_state()->log_reg_write.clear();
  this->get_state()->log_mem_read.clear();
  this->get_state()->log_mem_pre_write.clear();
}

bool Processor::will_trigger_interrupt(reg_t mip) {
  state_t *state = this->get_state();

  uint32_t old_mip = state->mip->read();
  uint32_t mie = state->mie->read();
  uint32_t mstatus = state->mstatus->read();
  uint32_t old_en_irq = old_mip & mie;
  uint32_t new_en_irq = mip & mie;


  // Only take interrupt if interrupt is enabled, not in debug mode, does not have a halt request, 
  // and the interrupt is new and not zero
  if( get_field(mstatus, MSTATUS_MIE) &&
      !state->debug_mode  &&
      (this->halt_request != processor_t::HR_REGULAR) &&
      //(old_en_irq == 0 ) && 
      (new_en_irq != 0)) 
  {
    return true;
  } else {
    return false;
  }
}

bool Processor::interrupt(reg_t mip, reg_t mie, uint32_t revert_steps, bool interrupt_allowed) {
  state_t *state = this->get_state();

  reg_t mask = 0xFFFF0888; // TODO: automatically generate this

  st_rvfi vref; //Passed to step, but not used

  this->interrupt_allowed = interrupt_allowed;

  state->mie->write_with_mask(mask, mie);

  if(interrupt_allowed && will_trigger_interrupt(mip)) {
    fprintf(this->get_log_file(), "interrupt mip %lx\n", mip);

    this->revert_step(revert_steps);

    state->mip->write_with_mask(mask, mip);

    // This step only sets the correct state for the interrupt, but does not actually execute an instruction
    // Another step needs to be taken to actually step through the instruction
    // Therefore we discard the rvfi values returned from this step
    this->step(1, vref);

    return true;
  } else {
    state->mip->write_with_mask(mask, mip);
    return false;
  }
 
}

bool Processor::set_debug(bool debug_req, uint32_t revert_steps, bool debug_allowed){
  bool debug_taken = false; 

  // NOTE: This is a workaround to allow the new debug to take over while the ebreak is still in the pipeline
  // If a new debug request is made while debug is allowed and a ebreak caused debug is active, disable debug mode to take the new debug.
  // When the ebread retires from the pipeline shell, debug_allowed will be 0, so this will only happen while the ebreak is still in the pipeline
  if(debug_req && debug_allowed && (this->state.dcsr->cause == DCSR_CAUSE_SWBP)) {
    this->state.debug_mode = 0; // Set debug mode to 0, to allow external debug to overwrite potetial ebreak caused debug
  }

  if(!(this->state.debug_mode) && debug_req && debug_allowed && (this->halt_request == HR_NONE)){
    this->halt_request = HR_REGULAR;
    debug_taken = true;
  } else if (this->state.debug_mode) {
    this->halt_request = HR_NONE;
  }
  

  if(debug_taken) {
    this->revert_step(revert_steps);
  }

  return debug_taken;
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

  string isa_str = this->params[base + "isa"].a_string;

  // Add _xdummy to enable bit 23 in MISA if non standard extensions are used
  if( (this->params[base+"nonstd_ext"]).a_bool) {
    isa_str = isa_str + "_xdummy";
  }

  string priv_str = this->params[base + "priv"].a_string;
  std::cout << "[SPIKE] Proc 0 | ISA: " << isa_str << " PRIV: " << priv_str << std::endl;
  this->isa =
      (const isa_parser_t *)new isa_parser_t(isa_str.c_str(), priv_str.c_str());

  disassembler = new disassembler_t(isa);

  for (auto e : isa->get_extensions()) {
    register_extension(e.second);
  }

  this->n_pmp = (this->params[base + "pmpregions"]).a_uint64_t;

  ((cfg_t *)cfg)->misaligned =
      (this->params[base + "misaligned"]).a_bool;


  this->csr_counters_injection =
      (this->params[base + "csr_counters_injection"]).a_bool;
  string extensions_str =
      (this->params[base + "extensions"]).a_string;

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

  uint64_t new_pc = (this->params[base + "boot_addr"]).a_uint64_t;
  this->state.pc = new_pc;

  this->put_csr(CSR_PMPADDR0, (this->params[base + "pmpaddr0"]).a_uint64_t);
  this->put_csr(CSR_PMPCFG0, (this->params[base + "pmpcfg0"]).a_uint64_t);

  this->state.csrmap[CSR_MVENDORID] =
      std::make_shared<const_csr_t>(this, CSR_MVENDORID, (this->params[base + "mvendorid"]).a_uint64_t);
  this->state.csrmap[CSR_MHARTID] =
      std::make_shared<const_csr_t>(this, CSR_MHARTID, (this->params[base + "mhartid"]).a_uint64_t);
  this->state.csrmap[CSR_MARCHID] =
      std::make_shared<const_csr_t>(this, CSR_MHARTID, (this->params[base + "marchid"]).a_uint64_t);

  bool fs_field_we_enable = (this->params[base + "status_fs_field_we_enable"]).a_bool;
  bool fs_field_we = (this->params[base + "status_fs_field_we"]).a_bool;
  bool vs_field_we_enable = (this->params[base + "status_vs_field_we_enable"]).a_bool;
  bool vs_field_we = (this->params[base + "status_vs_field_we"]).a_bool;

  reg_t sstatus_mask = this->state.mstatus->get_param_write_mask();
  if (fs_field_we_enable)
    sstatus_mask = (fs_field_we ? (sstatus_mask | MSTATUS_FS)
                                : (sstatus_mask & ~MSTATUS_FS));
  if (vs_field_we_enable)
    sstatus_mask = (vs_field_we ? (sstatus_mask | MSTATUS_VS)
                                : (sstatus_mask & ~MSTATUS_VS));
  this->state.mstatus->set_param_write_mask(sstatus_mask);

  bool misa_we_enable =
      (this->params[base + "misa_we_enable"]).a_bool;
  bool misa_we = (this->params[base + "misa_we"]).a_bool;
  if (misa_we_enable)
    this->state.misa->set_we(misa_we);

  this->next_rvfi_intr = 0;

  this->max_previous_states = (this->params[base + "num_prev_states_stored"]).a_uint64_t;

}

void Processor::take_trap(trap_t &t, reg_t epc) {
  this->taken_trap = true;
  this->which_trap = t.cause();
  processor_t::take_trap(t, epc);
}

Processor::~Processor() { delete this->isa; }

void Processor::default_params(string base, openhw::Params &params) {
  params.set_string(base, "isa", "RV32GC", "RV32GC",
             "ISA");
  params.set_string(base, "priv", DEFAULT_PRIV,
             DEFAULT_PRIV, "Privilege Level");
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
  params.set_bool(base, "misa_we_enable", true, "true",
             "MISA CSR Write Enable param enable");
  params.set_bool(base, "misa_we", false, "false",
             "MISA CSR Write Enable value");

  params.set_bool(base, "misaligned", false, "false",
             "Support for misaligned memory operations");

  params.set_bool(base, "csr_counters_injection", false, "false",
             "Allow to set CSRs getting values from a DPI");

  params.set_bool(base, "nonstd_ext", false, "false",
             "Non-standard extension used");

  params.set_uint64_t(base, "num_prev_states_stored", 0UL, "0",
             "The number of previous states stored for reverting");

}

inline void Processor::set_XPR(reg_t num, reg_t value) {
  this->state.XPR.write(num, value);
}

inline void Processor::set_FPR(reg_t num, float128_t value) {
  this->state.FPR.write(num, value);
}

} // namespace openhw
