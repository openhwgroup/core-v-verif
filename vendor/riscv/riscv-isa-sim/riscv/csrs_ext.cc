// See LICENSE for license details.

// For std::any_of
#include <algorithm>

// For processor_t:
#include "mmu.h"
#include "processor.h"
#include "Proc.h"
// For get_field():
#include "decode_macros.h"
// For trap_virtual_instruction and trap_illegal_instruction:
#include "trap.h"
// For require():
#include "insn_macros.h"

// STATE macro used by require_privilege() macro:
#undef STATE
#define STATE (*state)

namespace openhw {
// implement a middle csr class
reg::reg(processor_t *const proc, const reg_t addr, const reg_t init)
    : address(addr), value(init), param_write_mask(-1), param_implemented(true),
      param_accessible(true),
      proc(proc), state(proc->get_state()), name("") {
          this->name = csr_t::addr2name(addr);
      }

void reg::set_param_write_mask(reg_t mask) noexcept {
  this->param_write_mask = mask;
}

reg_t reg::get_param_write_mask() noexcept { return this->param_write_mask; }

bool reg::post_read(const reg_t &val) const noexcept { return true; }

bool reg::pre_write(const reg_t &val) noexcept {
  const reg_t curr = this->unlogged_read();
  const reg_t new_val =
      (val & this->param_write_mask) | (curr & ~this->param_write_mask);
  *((reg_t *)&val) = new_val;

  return true;
}

bool reg::post_write(const reg_t &val) noexcept {
    // Implement MTVEC alignment parameter
    if (address == CSR_MTVEC) {
        reg_t value = this->unlogged_read();
        if (value & 1) {
            string param_str = ((Processor*)this->proc)->get_base() + "mtvec_vectored_alignment";
            reg_t align = ((Processor*)this->proc)->get_params()[param_str].a_uint64_t;
            reg_t mask = ~(align - 1);
            reg_t new_val = (value & mask) | 1;
            this->unlogged_write(new_val);
        }
    }
    else if (address == CSR_MIE || address == CSR_MIP) {
        reg_t value = this->unlogged_read();
        string param_str = ((Processor*)this->proc)->get_base() + "non_standard_interrupts";
        bool clic_mode = ((Processor*)this->proc)->get_params()[param_str].a_bool;
        if (clic_mode) {
            reg_t mask = (0x10000 - 0x1);
            reg_t new_val = (value & mask) | (val & ~mask);
            this->backdoor_write(new_val);
            log_write();
        }

    }

    return true;
}


bool reg::custom_checks(insn_t insn, bool write) const {
  return true;
}

inline reg_t reg::unlogged_read() const noexcept {
  auto ret_val = this->value;
  return ret_val;
}

inline bool reg::unlogged_write(reg_t val) noexcept {
  this->value = val;
  return true;
}

inline bool reg::backdoor_write(reg_t val) noexcept {
  this->value = val;
  return true;
}

inline string reg::get_name() noexcept {
  return this->name;
}

inline void reg::set_name(string new_name) noexcept {
  this->name = new_name;
}

void reg::write(const reg_t val, const bool log) noexcept {
  if (!this->param_implemented)
    return;

  this->pre_write(val);
  const bool success = unlogged_write(val);
  this->post_write(val);

  if (success && log) {
    log_write();
  }
}
void reg::log_write() const noexcept {}

reg_t reg::read() const noexcept {
  auto ret_val = this->unlogged_read();
  this->post_read(ret_val);
  return ret_val;
}

std::string reg::addr2name(uint64_t addr) {
    switch(addr) {
        case CSR_FFLAGS         : return "fflags";
        case CSR_FRM            : return "frm";
        case CSR_FCSR           : return "fcsr";
        case CSR_CYCLE          : return "cycle";
        case CSR_TIME           : return "time";
        case CSR_INSTRET        : return "instret";
        case CSR_HPMCOUNTER3    : return "hpmcounter3";
        case CSR_HPMCOUNTER4    : return "hpmcounter4";
        case CSR_HPMCOUNTER5    : return "hpmcounter5";
        case CSR_HPMCOUNTER6    : return "hpmcounter6";
        case CSR_HPMCOUNTER7    : return "hpmcounter7";
        case CSR_HPMCOUNTER8    : return "hpmcounter8";
        case CSR_HPMCOUNTER9    : return "hpmcounter9";
        case CSR_HPMCOUNTER10   : return "hpmcounter10";
        case CSR_HPMCOUNTER11   : return "hpmcounter11";
        case CSR_HPMCOUNTER12   : return "hpmcounter12";
        case CSR_HPMCOUNTER13   : return "hpmcounter13";
        case CSR_HPMCOUNTER14   : return "hpmcounter14";
        case CSR_HPMCOUNTER15   : return "hpmcounter15";
        case CSR_HPMCOUNTER16   : return "hpmcounter16";
        case CSR_HPMCOUNTER17   : return "hpmcounter17";
        case CSR_HPMCOUNTER18   : return "hpmcounter18";
        case CSR_HPMCOUNTER19   : return "hpmcounter19";
        case CSR_HPMCOUNTER20   : return "hpmcounter20";
        case CSR_HPMCOUNTER21   : return "hpmcounter21";
        case CSR_HPMCOUNTER22   : return "hpmcounter22";
        case CSR_HPMCOUNTER23   : return "hpmcounter23";
        case CSR_HPMCOUNTER24   : return "hpmcounter24";
        case CSR_HPMCOUNTER25   : return "hpmcounter25";
        case CSR_HPMCOUNTER26   : return "hpmcounter26";
        case CSR_HPMCOUNTER27   : return "hpmcounter27";
        case CSR_HPMCOUNTER28   : return "hpmcounter28";
        case CSR_HPMCOUNTER29   : return "hpmcounter29";
        case CSR_HPMCOUNTER30   : return "hpmcounter30";
        case CSR_HPMCOUNTER31   : return "hpmcounter31";
        case CSR_CYCLEH         : return "cycleh";
        case CSR_TIMEH          : return "timeh";
        case CSR_INSTRETH       : return "instreth";
        case CSR_HPMCOUNTER3H   : return "hpmcounter3h";
        case CSR_HPMCOUNTER4H   : return "hpmcounter4h";
        case CSR_HPMCOUNTER5H   : return "hpmcounter5h";
        case CSR_HPMCOUNTER6H   : return "hpmcounter6h";
        case CSR_HPMCOUNTER7H   : return "hpmcounter7h";
        case CSR_HPMCOUNTER8H   : return "hpmcounter8h";
        case CSR_HPMCOUNTER9H   : return "hpmcounter9h";
        case CSR_HPMCOUNTER10H  : return "hpmcounter10h";
        case CSR_HPMCOUNTER11H  : return "hpmcounter11h";
        case CSR_HPMCOUNTER12H  : return "hpmcounter12h";
        case CSR_HPMCOUNTER13H  : return "hpmcounter13h";
        case CSR_HPMCOUNTER14H  : return "hpmcounter14h";
        case CSR_HPMCOUNTER15H  : return "hpmcounter15h";
        case CSR_HPMCOUNTER16H  : return "hpmcounter16h";
        case CSR_HPMCOUNTER17H  : return "hpmcounter17h";
        case CSR_HPMCOUNTER18H  : return "hpmcounter18h";
        case CSR_HPMCOUNTER19H  : return "hpmcounter19h";
        case CSR_HPMCOUNTER20H  : return "hpmcounter20h";
        case CSR_HPMCOUNTER21H  : return "hpmcounter21h";
        case CSR_HPMCOUNTER22H  : return "hpmcounter22h";
        case CSR_HPMCOUNTER23H  : return "hpmcounter23h";
        case CSR_HPMCOUNTER24H  : return "hpmcounter24h";
        case CSR_HPMCOUNTER25H  : return "hpmcounter25h";
        case CSR_HPMCOUNTER26H  : return "hpmcounter26h";
        case CSR_HPMCOUNTER27H  : return "hpmcounter27h";
        case CSR_HPMCOUNTER28H  : return "hpmcounter28h";
        case CSR_HPMCOUNTER29H  : return "hpmcounter29h";
        case CSR_HPMCOUNTER30H  : return "hpmcounter30h";
        case CSR_HPMCOUNTER31H  : return "hpmcounter31h";
        case CSR_SSTATUS        : return "sstatus";
        case CSR_SEDELEG        : return "sedeleg";
        case CSR_SIDELEG        : return "sideleg";
        case CSR_SIE            : return "sie";
        case CSR_STVEC          : return "stvec";
        case CSR_SCOUNTEREN     : return "scounteren";
        case CSR_SSCRATCH       : return "sscratch";
        case CSR_SEPC           : return "sepc";
        case CSR_SCAUSE         : return "scause";
        case CSR_STVAL          : return "stval";
        case CSR_SIP            : return "sip";
        case CSR_SATP           : return "satp";
        case CSR_MVENDORID      : return "mvendorid";
        case CSR_MARCHID        : return "marchid";
        case CSR_MIMPID         : return "mimpid";
        case CSR_MHARTID        : return "mhartid";
        case CSR_MSTATUS        : return "mstatus";
        case CSR_MISA           : return "misa";
        case CSR_MEDELEG        : return "medeleg";
        case CSR_MIDELEG        : return "mideleg";
        case CSR_MIE            : return "mie";
        case CSR_MTVEC          : return "mtvec";
        case CSR_MCOUNTEREN     : return "mcounteren";
        case CSR_MENVCFG        : return "menvcfg";
        case CSR_MSTATUSH       : return "mstatush";
        case CSR_MENVCFGH       : return "menvcfgh";
        case CSR_MSCRATCH       : return "mscratch";
        case CSR_MEPC           : return "mepc";
        case CSR_MCAUSE         : return "mcause";
        case CSR_MTVAL          : return "mtval";
        case CSR_MIP            : return "mip";
        case CSR_MTINST         : return "mtinst";
        case CSR_MTVAL2         : return "mtval2";
        case CSR_PMPCFG0        : return "pmpcfg0";
        case CSR_PMPCFG1        : return "pmpcfg1";
        case CSR_PMPCFG2        : return "pmpcfg2";
        case CSR_PMPCFG3        : return "pmpcfg3";
        case CSR_PMPCFG4        : return "pmpcfg4";
        case CSR_PMPCFG5        : return "pmpcfg5";
        case CSR_PMPCFG6        : return "pmpcfg6";
        case CSR_PMPCFG7        : return "pmpcfg7";
        case CSR_PMPCFG8        : return "pmpcfg8";
        case CSR_PMPCFG9        : return "pmpcfg9";
        case CSR_PMPCFG10       : return "pmpcfg10";
        case CSR_PMPCFG11       : return "pmpcfg11";
        case CSR_PMPCFG12       : return "pmpcfg12";
        case CSR_PMPCFG13       : return "pmpcfg13";
        case CSR_PMPCFG14       : return "pmpcfg14";
        case CSR_PMPCFG15       : return "pmpcfg15";
        case CSR_PMPADDR0       : return "pmpaddr0";
        case CSR_PMPADDR1       : return "pmpaddr1";
        case CSR_PMPADDR2       : return "pmpaddr2";
        case CSR_PMPADDR3       : return "pmpaddr3";
        case CSR_PMPADDR4       : return "pmpaddr4";
        case CSR_PMPADDR5       : return "pmpaddr5";
        case CSR_PMPADDR6       : return "pmpaddr6";
        case CSR_PMPADDR7       : return "pmpaddr7";
        case CSR_PMPADDR8       : return "pmpaddr8";
        case CSR_PMPADDR9       : return "pmpaddr9";
        case CSR_PMPADDR10      : return "pmpaddr10";
        case CSR_PMPADDR11      : return "pmpaddr11";
        case CSR_PMPADDR12      : return "pmpaddr12";
        case CSR_PMPADDR13      : return "pmpaddr13";
        case CSR_PMPADDR14      : return "pmpaddr14";
        case CSR_PMPADDR15      : return "pmpaddr15";
        case CSR_PMPADDR16      : return "pmpaddr16";
        case CSR_PMPADDR17      : return "pmpaddr17";
        case CSR_PMPADDR18      : return "pmpaddr18";
        case CSR_PMPADDR19      : return "pmpaddr19";
        case CSR_PMPADDR20      : return "pmpaddr20";
        case CSR_PMPADDR21      : return "pmpaddr21";
        case CSR_PMPADDR22      : return "pmpaddr22";
        case CSR_PMPADDR23      : return "pmpaddr23";
        case CSR_PMPADDR24      : return "pmpaddr24";
        case CSR_PMPADDR25      : return "pmpaddr25";
        case CSR_PMPADDR26      : return "pmpaddr26";
        case CSR_PMPADDR27      : return "pmpaddr27";
        case CSR_PMPADDR28      : return "pmpaddr28";
        case CSR_PMPADDR29      : return "pmpaddr29";
        case CSR_PMPADDR30      : return "pmpaddr30";
        case CSR_PMPADDR31      : return "pmpaddr31";
        case CSR_PMPADDR32      : return "pmpaddr32";
        case CSR_PMPADDR33      : return "pmpaddr33";
        case CSR_PMPADDR34      : return "pmpaddr34";
        case CSR_PMPADDR35      : return "pmpaddr35";
        case CSR_PMPADDR36      : return "pmpaddr36";
        case CSR_PMPADDR37      : return "pmpaddr37";
        case CSR_PMPADDR38      : return "pmpaddr38";
        case CSR_PMPADDR39      : return "pmpaddr39";
        case CSR_PMPADDR40      : return "pmpaddr40";
        case CSR_PMPADDR41      : return "pmpaddr41";
        case CSR_PMPADDR42      : return "pmpaddr42";
        case CSR_PMPADDR43      : return "pmpaddr43";
        case CSR_PMPADDR44      : return "pmpaddr44";
        case CSR_PMPADDR45      : return "pmpaddr45";
        case CSR_PMPADDR46      : return "pmpaddr46";
        case CSR_PMPADDR47      : return "pmpaddr47";
        case CSR_PMPADDR48      : return "pmpaddr48";
        case CSR_PMPADDR49      : return "pmpaddr49";
        case CSR_PMPADDR50      : return "pmpaddr50";
        case CSR_PMPADDR51      : return "pmpaddr51";
        case CSR_PMPADDR52      : return "pmpaddr52";
        case CSR_PMPADDR53      : return "pmpaddr53";
        case CSR_PMPADDR54      : return "pmpaddr54";
        case CSR_PMPADDR55      : return "pmpaddr55";
        case CSR_PMPADDR56      : return "pmpaddr56";
        case CSR_PMPADDR57      : return "pmpaddr57";
        case CSR_PMPADDR58      : return "pmpaddr58";
        case CSR_PMPADDR59      : return "pmpaddr59";
        case CSR_PMPADDR60      : return "pmpaddr60";
        case CSR_PMPADDR61      : return "pmpaddr61";
        case CSR_PMPADDR62      : return "pmpaddr62";
        case CSR_PMPADDR63      : return "pmpaddr63";
        case CSR_MCYCLE         : return "mcycle";
        case CSR_MINSTRET       : return "minstret";
        case CSR_MHPMCOUNTER3   : return "mhpmcounter3";
        case CSR_MHPMCOUNTER4   : return "mhpmcounter4";
        case CSR_MHPMCOUNTER5   : return "mhpmcounter5";
        case CSR_MHPMCOUNTER6   : return "mhpmcounter6";
        case CSR_MHPMCOUNTER7   : return "mhpmcounter7";
        case CSR_MHPMCOUNTER8   : return "mhpmcounter8";
        case CSR_MHPMCOUNTER9   : return "mhpmcounter9";
        case CSR_MHPMCOUNTER10  : return "mhpmcounter10";
        case CSR_MHPMCOUNTER11  : return "mhpmcounter11";
        case CSR_MHPMCOUNTER12  : return "mhpmcounter12";
        case CSR_MHPMCOUNTER13  : return "mhpmcounter13";
        case CSR_MHPMCOUNTER14  : return "mhpmcounter14";
        case CSR_MHPMCOUNTER15  : return "mhpmcounter15";
        case CSR_MHPMCOUNTER16  : return "mhpmcounter16";
        case CSR_MHPMCOUNTER17  : return "mhpmcounter17";
        case CSR_MHPMCOUNTER18  : return "mhpmcounter18";
        case CSR_MHPMCOUNTER19  : return "mhpmcounter19";
        case CSR_MHPMCOUNTER20  : return "mhpmcounter20";
        case CSR_MHPMCOUNTER21  : return "mhpmcounter21";
        case CSR_MHPMCOUNTER22  : return "mhpmcounter22";
        case CSR_MHPMCOUNTER23  : return "mhpmcounter23";
        case CSR_MHPMCOUNTER24  : return "mhpmcounter24";
        case CSR_MHPMCOUNTER25  : return "mhpmcounter25";
        case CSR_MHPMCOUNTER26  : return "mhpmcounter26";
        case CSR_MHPMCOUNTER27  : return "mhpmcounter27";
        case CSR_MHPMCOUNTER28  : return "mhpmcounter28";
        case CSR_MHPMCOUNTER29  : return "mhpmcounter29";
        case CSR_MHPMCOUNTER30  : return "mhpmcounter30";
        case CSR_MHPMCOUNTER31  : return "mhpmcounter31";
        case CSR_MCYCLEH        : return "mcycleh";
        case CSR_MINSTRETH      : return "minstreth";
        case CSR_MHPMCOUNTER3H  : return "mhpmcounter3h";
        case CSR_MHPMCOUNTER4H  : return "mhpmcounter4h";
        case CSR_MHPMCOUNTER5H  : return "mhpmcounter5h";
        case CSR_MHPMCOUNTER6H  : return "mhpmcounter6h";
        case CSR_MHPMCOUNTER7H  : return "mhpmcounter7h";
        case CSR_MHPMCOUNTER8H  : return "mhpmcounter8h";
        case CSR_MHPMCOUNTER9H  : return "mhpmcounter9h";
        case CSR_MHPMCOUNTER10H : return "mhpmcounter10h";
        case CSR_MHPMCOUNTER11H : return "mhpmcounter11h";
        case CSR_MHPMCOUNTER12H : return "mhpmcounter12h";
        case CSR_MHPMCOUNTER13H : return "mhpmcounter13h";
        case CSR_MHPMCOUNTER14H : return "mhpmcounter14h";
        case CSR_MHPMCOUNTER15H : return "mhpmcounter15h";
        case CSR_MHPMCOUNTER16H : return "mhpmcounter16h";
        case CSR_MHPMCOUNTER17H : return "mhpmcounter17h";
        case CSR_MHPMCOUNTER18H : return "mhpmcounter18h";
        case CSR_MHPMCOUNTER19H : return "mhpmcounter19h";
        case CSR_MHPMCOUNTER20H : return "mhpmcounter20h";
        case CSR_MHPMCOUNTER21H : return "mhpmcounter21h";
        case CSR_MHPMCOUNTER22H : return "mhpmcounter22h";
        case CSR_MHPMCOUNTER23H : return "mhpmcounter23h";
        case CSR_MHPMCOUNTER24H : return "mhpmcounter24h";
        case CSR_MHPMCOUNTER25H : return "mhpmcounter25h";
        case CSR_MHPMCOUNTER26H : return "mhpmcounter26h";
        case CSR_MHPMCOUNTER27H : return "mhpmcounter27h";
        case CSR_MHPMCOUNTER28H : return "mhpmcounter28h";
        case CSR_MHPMCOUNTER29H : return "mhpmcounter29h";
        case CSR_MHPMCOUNTER30H : return "mhpmcounter30h";
        case CSR_MHPMCOUNTER31H : return "mhpmcounter31h";
        case CSR_MCOUNTINHIBIT  : return "mcountinhibit";
        case CSR_MHPMEVENT3     : return "mhpmevent3";
        case CSR_MHPMEVENT4     : return "mhpmevent4";
        case CSR_MHPMEVENT5     : return "mhpmevent5";
        case CSR_MHPMEVENT6     : return "mhpmevent6";
        case CSR_MHPMEVENT7     : return "mhpmevent7";
        case CSR_MHPMEVENT8     : return "mhpmevent8";
        case CSR_MHPMEVENT9     : return "mhpmevent9";
        case CSR_MHPMEVENT10    : return "mhpmevent10";
        case CSR_MHPMEVENT11    : return "mhpmevent11";
        case CSR_MHPMEVENT12    : return "mhpmevent12";
        case CSR_MHPMEVENT13    : return "mhpmevent13";
        case CSR_MHPMEVENT14    : return "mhpmevent14";
        case CSR_MHPMEVENT15    : return "mhpmevent15";
        case CSR_MHPMEVENT16    : return "mhpmevent16";
        case CSR_MHPMEVENT17    : return "mhpmevent17";
        case CSR_MHPMEVENT18    : return "mhpmevent18";
        case CSR_MHPMEVENT19    : return "mhpmevent19";
        case CSR_MHPMEVENT20    : return "mhpmevent20";
        case CSR_MHPMEVENT21    : return "mhpmevent21";
        case CSR_MHPMEVENT22    : return "mhpmevent22";
        case CSR_MHPMEVENT23    : return "mhpmevent23";
        case CSR_MHPMEVENT24    : return "mhpmevent24";
        case CSR_MHPMEVENT25    : return "mhpmevent25";
        case CSR_MHPMEVENT26    : return "mhpmevent26";
        case CSR_MHPMEVENT27    : return "mhpmevent27";
        case CSR_MHPMEVENT28    : return "mhpmevent28";
        case CSR_MHPMEVENT29    : return "mhpmevent29";
        case CSR_MHPMEVENT30    : return "mhpmevent30";
        case CSR_MHPMEVENT31    : return "mhpmevent31";
        case CSR_MSECCFG        : return "mseccfg";
        case CSR_MSECCFGH       : return "mseccfgh";
        case CSR_TSELECT        : return "tselect";
        case CSR_TDATA1         : return "tdata1";
        case CSR_TDATA2         : return "tdata2";
        case CSR_TDATA3         : return "tdata3";
        case CSR_TINFO          : return "tinfo";
        case CSR_TCONTROL       : return "tcontrol";
        case CSR_MCONTEXT       : return "mcontext";
        case CSR_SCONTEXT       : return "scontext";
        case CSR_DCSR           : return "dcsr";
        case CSR_DPC            : return "dpc";
        case CSR_DSCRATCH0      : return "dscratch0";
        case CSR_DSCRATCH1      : return "dscratch1";
        case CSR_VSTART         : return "vstart";
        case CSR_VXSAT          : return "vxsat";
        case CSR_VXRM           : return "vxrm";
        case CSR_VL             : return "vl";
        case CSR_VTYPE          : return "vtype";
        case CSR_VLENB          : return "vlenb";
        case CSR_MCONFIGPTR     : return "mconfigptr";
        // Old CSR
        case CSR_MSCONTEXT      : return "mscontext";
    }
    return "";
};

void reg::set_param_accessible(bool accessible) noexcept { this->param_accessible = accessible; }

void reg::set_param_implemented(bool implemented) noexcept { this->param_implemented = implemented; }


} // namespace openhw
