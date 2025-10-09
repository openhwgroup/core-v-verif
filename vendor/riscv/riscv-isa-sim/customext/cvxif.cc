// Copyright (C) 2022 Thales DIS Design Services SAS
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0.
//
// Original Author: Zbigniew CHAMSKI <zbigniew.chamski@thalesgroup.com>

// Name of this extension as seen internally by Spike
#define EXTENSION_NAME "cvxif"

#define DECODE_MACRO_USAGE_LOGGED 1
#include "decode_macros.h"
#include "encoding.h"
#include "insn_macros.h"
#include "cvxif.h"
#include "mmu.h"
#include <cstring>
#include "Proc.h"
#include "Params.h"

// Define custom insns templates.
// The insn-level wrapper is 'c##n' (default implementation,
// writeback disabled), the default implementation
// is 'custom##n': illegal instruction, return 0.
// The writeback controller 'cvxif_extn_t::do_writeback_p'
// is in charge of determining if writeback is required or not.
// After executing the instruction the PC is avanced by 4 bytes.
#define customX(n) \
static reg_t c##n(processor_t* p, insn_t insn, reg_t pc) \
  { \
    cvxif_t* cvxif = static_cast<cvxif_t*>(p->get_extension(EXTENSION_NAME)); \
    require_extension(EXT_XCVXIF); \
    reg_t xd = cvxif->default_custom##n(insn); \
    if (cvxif->do_writeback_p(insn)) \
      WRITE_RD(xd); \
    return pc+4; \
  } \
  \
  reg_t default_custom##n(insn_t insn) \
  { \
    return custom##n(insn); \
  }

// Define 32-bit insn template with explicit RD.
// The insn-level wrapper is 'cvxif_32_##<name>',
// the default implementation is 'default_cvxif_32_##<name>'
// and the register semantics is expected in function 'compute_cvxif_32_##<name>'.
// After executing the instruction the PC is advanced by 4 bytes.
#define cvxif_insn_32(name) \
  static reg_t cvxif_32_##name(processor_t* p, insn_t insn, reg_t pc) { \
    require_extension(EXT_XCVXIF); \
    cvxif_t* cvxif = static_cast<cvxif_t*>(p->get_extension(EXTENSION_NAME)); \
    reg_t xd = cvxif->default_cvxif_32_##name(insn); \
    if (cvxif->do_writeback_p(insn)) \
      WRITE_RD(xd); \
    return pc+4; \
  } \
  \
  reg_t default_cvxif_32_##name(insn_t insn) { \
    return cvxif_##name(insn); \
  }

// Define 32-bit insn template with implicit RD == a0.
// Like 'cvxif_insn_32' but the destination register is hardcoded.
// After executing the instruction the PC is advanced by 4 bytes.
#define cvxif_insn_32_rd_implicit_a0(name) \
  static reg_t cvxif_32_##name(processor_t* p, insn_t insn, reg_t pc) { \
    cvxif_t* cvxif = static_cast<cvxif_t*>(p->get_extension(EXTENSION_NAME)); \
    require_extension(EXT_XCVXIF); \
    reg_t xd = cvxif->default_cvxif_32_##name(insn); \
    if (cvxif->do_writeback_p(insn)) \
      WRITE_REG(10, xd); \
    return pc+4; \
  } \
  \
  reg_t default_cvxif_32_##name(insn_t insn) { \
    return cvxif_##name(insn); \
  }

// Like the 32-bit explicit RD version 'cvxif_insn_32', but uses 16-bit
// opcodes. PC is advanced by 16 bits instead of 32.
#define cvxif_insn_16(name) \
  static reg_t cvxif_16_##name(processor_t* p, insn_t insn, reg_t pc) { \
    cvxif_t* cvxif = static_cast<cvxif_t*>(p->get_extension(EXTENSION_NAME)); \
    require_extension(EXT_XCVXIF); \
    reg_t xd = cvxif->default_cvxif_16_##name(insn); \
    if (cvxif->do_writeback_p(insn)) \
      WRITE_RD(xd); \
    return pc+2; \
  } \
  \
  reg_t default_cvxif_16_##name(insn_t insn) { \
    return cvxif_##name(insn); \
  }

// Like 'cvxif_insn_16', but RD is implicitly x10 (a0).
// PC is advanced by 16 bits.
#define cvxif_insn_16_rd_implicit_a0(name) \
  static reg_t cvxif_16_##name(processor_t* p, insn_t insn, reg_t pc) { \
    cvxif_t* cvxif = static_cast<cvxif_t*>(p->get_extension(EXTENSION_NAME)); \
    require_extension(EXT_XCVXIF); \
    reg_t xd = cvxif->default_cvxif_16_##name(insn); \
    if (cvxif->do_writeback_p(insn)) \
      WRITE_REG(10, xd); \
    return pc+2; \
  } \
  \
  reg_t default_cvxif_16_##name(insn_t insn) { \
    return cvxif_##name(insn); \
  }

// This class instantiates the CV-X-IF interface.
class cvxif_t : public cvxif_extn_t
{
 public:
  const char* name() { return EXTENSION_NAME; }

  bool do_writeback_p(insn_t insn)
  {
    // Convert the RISC-V insn to a more generic type 'cvxif_insn_t'.
    // INSN_R personality serves to simplify access to standard encoding fields.
    cvxif_insn_t copro_insn = { .i = insn };
    cvxif_r_insn_t insn_r = copro_insn.r_type;

    if ((insn_r.opcode & 0x3) != (unsigned) Cop::NOT_COMPRESSED) {
      // Instruction is compressed.  Only CUS_CADD writes back something.
      if (copro_insn.cr_type.opcode == Cop::C0) {
        // Compressed insns with opcode C0 (2'b10) used in CV-X-IF:
        // - CUS_CNOP: no WB
        // - CUS_CADD: writes back into x10.
        if (copro_insn.cr_type.funct4 == Func4::FUNC4_CADD)
          return true;
      }
      // All other compressed insns.
      return false;
    } else if (insn_r.opcode == 0x7b /* MATCH_CUSTOM3 */) {
      switch (insn_r.funct3) {
        case Func3::FUNC3_0:
          //CUS_NOP have rd equal to zero
          return (insn_r.rd != 0x0);
        case Func3::FUNC3_1:
          switch (insn_r.funct7) {
            case Func7::CUS_ADD:
              return true;
            case Func7::CUS_DOUBLE_RS1:
              return true;
            case Func7::CUS_DOUBLE_RS2:
             return true;
            case Func7::CUS_ADD_MULTI:
              return true;
            default:
              return false;
          }
        default:
          // All other values of Func3
          return false;
      }
    } else if (insn_r.funct3 == 0x0
               && (insn_r.funct7 & 0x3) == 0x0) {
      // Potential CVXIF opcodes
#if 1
      switch (insn_r.opcode) {
        case CustomOpcode::CUS_ADD_RS3_MADDRTYPE:
        case CustomOpcode::CUS_ADD_RS3_MSUB:
        case CustomOpcode::CUS_ADD_RS3_NMADD:
        case CustomOpcode::CUS_ADD_RS3_NMSUB:
          return true;
        default:
          return false;
      }
#endif
    } else if (insn_r.opcode == CustomOpcode::CUS_ADD_RS3_MADDRTYPE
               && insn_r.funct3 == 0x1
               && insn_r.funct7 == Func7::CUS_ADD_RS3_RTYPE)
      return true;

    // Catch-all clause
    return false;
  }

  // Custom0 instructions: default behaviour.
  reg_t custom0(insn_t incoming_insn)
  {
    illegal_instruction();
    return -1;
  }

  // Custom1 instructions: default behaviour.
  reg_t custom1(insn_t incoming_insn)
  {
    illegal_instruction();
    return -1;
  }

  // Custom2 instructions: default behaviour.
  reg_t custom2(insn_t incoming_insn)
  {
    illegal_instruction();
    return -1;
  }

  // Custom3 instructions: provide an explicit implementation of decode+exec.
  reg_t custom3(insn_t insn)
  {
    // Convert insn to a more general type 'cvxif_insn_t'.
    cvxif_insn_t incoming_insn = { .i = insn };
    // Assume R-type insn: it shares opcode and funct3 fields with other CVXIF insn formats.
    cvxif_r_insn_t r_insn = incoming_insn.r_type;

    switch (r_insn.funct3)
    {
      case FUNC3_0:
          switch (r_insn.funct7)
          {
            // CUS_NOP
            case (0x00):
              break;
            default:
              illegal_instruction();
          }
      case FUNC3_1:
        switch(r_insn.funct7) {
          case Func7::CUS_ADD:
            return (reg_t) sext_xlen((sreg_t) RS1 + (sreg_t) RS2);
          case Func7::CUS_DOUBLE_RS1:
            return (reg_t) sext_xlen((sreg_t) RS1 + (sreg_t) RS1);
          case Func7::CUS_DOUBLE_RS2:
            return (reg_t) sext_xlen((sreg_t) RS2 + (sreg_t) RS2);
          case Func7::CUS_ADD_MULTI:
            return (reg_t) sext_xlen((sreg_t) RS1 + (sreg_t) RS2);
          default:
            illegal_instruction();
        }
      default:
        illegal_instruction();
    }

    // FORNOW: Return 0xf......f to simplify debugging.
    return (reg_t) -1;
  };

  // Computation semantics of CUS_ADD_RS3_MADD: Custom Add with RS3, opcode == MADD.
  // Add RS2 and RS3 to RS1.  Ignore RS3 if x_num_rs is not 3.
  reg_t cvxif_cus_add_rs3_madd(insn_t insn)
  {
    reg_t result = (reg_t) sext_xlen((sreg_t) RS1 + (sreg_t) RS2 + (sreg_t) (x_num_rs == 3 ? RS3 : 0));
    std::cerr << "### [SPIKE] cvxif_cus_add_rs3_madd(x" << std::dec << insn.rs1() << " = 0x" << std::hex << (reg_t) RS1 <<
                                                  ", x" << std::dec << insn.rs2() << " = 0x" << std::hex << (reg_t) RS2 <<
                                                  ", x" << std::dec << insn.rs3() << " = 0x" << std::hex << (reg_t) RS3 <<
                                                  " /* X_NUM_RS == " << std::dec << x_num_rs <<
                                                  " */ ) = 0x" << std::hex << result << " -> x" << std::dec << insn.rd() << std::endl;
    return result;
  };

  // Computation semantics of CUS_ADD_RS3_MSUB: Custom Add with RS3, opcode == MSUB.
  // Subtract RS2 and RS3 from RS1.  Ignore RS3 if x_num_rs is not 3.
  reg_t cvxif_cus_add_rs3_msub(insn_t insn)
  {
    reg_t result = (reg_t) sext_xlen((sreg_t) RS1 - (sreg_t) RS2 - (sreg_t) (x_num_rs == 3 ? RS3 : 0));
    std::cerr << "### [SPIKE] cvxif_cus_add_rs3_msub(x" << std::dec << insn.rs1() << " = 0x" << std::hex << (reg_t) RS1 <<
                                                  ", x" << std::dec << insn.rs2() << " = 0x" << std::hex << (reg_t) RS2 <<
                                                  ", x" << std::dec << insn.rs3() << " = 0x" << std::hex << (reg_t) RS3 <<
                                                  " /* X_NUM_RS == " << std::dec << x_num_rs <<
                                                  " */ ) = 0x" << std::hex << result << " -> x" << std::dec << insn.rd() << std::endl;
    return result;
  };

  // Computation semantics of CUS_ADD_RS3_NMADD: Custom Add with RS3, opcode == NMADD.
  // Add RS2 and RS3 to RS1, then negate result bitwise.  Ignore RS3 if x_num_rs is not 3.
  reg_t cvxif_cus_add_rs3_nmadd(insn_t insn)
  {
    reg_t result = (reg_t) sext_xlen(~((sreg_t) RS1 + (sreg_t) RS2 + (sreg_t) (x_num_rs == 3 ? RS3 : 0)));
    std::cerr << "### [SPIKE] cvxif_cus_add_rs3_nmadd(x" << std::dec << insn.rs1() << " = 0x" << std::hex << (reg_t) RS1 <<
                                                    ", x" << std::dec << insn.rs2() << " = 0x" << std::hex << (reg_t) RS2 <<
                                                    ", x" << std::dec << insn.rs3() << " = 0x" << std::hex << (reg_t) RS3 <<
                                                    " /* X_NUM_RS == " << std::dec << x_num_rs <<
                                                    " */ ) = 0x" << std::hex << result << " -> x" << std::dec << insn.rd() << std::endl;
    return result;
  };

  // Semantics of CUS_ADD_RS3_NMSUB: Custom Add with RS3, opcode == NMSUB.
  // Subtract RS2 and RS3 from RS1, then negate result bitwise.  Ignore RS3 if x_num_rs is not 3.
  reg_t cvxif_cus_add_rs3_nmsub(insn_t insn)
  {
    reg_t result = (reg_t) sext_xlen(~((sreg_t) RS1 - (sreg_t) RS2 - (sreg_t) (x_num_rs == 3 ? RS3 : 0)));
    std::cerr << "### [SPIKE] cvxif_cus_add_rs3_nmsub(x" << std::dec << insn.rs1() << " = 0x" << std::hex << (reg_t) RS1 <<
                                                    ", x" << std::dec << insn.rs2() << " = 0x" << std::hex << (reg_t) RS2 <<
                                                    ", x" << std::dec << insn.rs3() << " = 0x" << std::hex << (reg_t) RS3 <<
                                                    " /* X_NUM_RS == " << std::dec << x_num_rs <<
                                                    " */ ) = 0x" << std::hex << result << " -> x" << std::dec << insn.rd() << std::endl;
    return result;
  };

  // Semantics of CUS_ADD_RS3_RTYPE: Custom Add with RS3, opcode == RTYPE.
  // Add RS2 and RS3 to RS1.  Ignore RS3 if x_num_rs is not 3.
  reg_t cvxif_cus_add_rs3_rtype(insn_t insn)
  {
    reg_t result = (reg_t) sext_xlen((sreg_t) RS1 + (sreg_t) RS2 + (sreg_t) (x_num_rs == 3 ? RS3 : 0));
    std::cerr << "### [SPIKE] cvxif_cus_add_rs3_rtype(x" << std::dec << insn.rs1() << " = 0x" << std::hex << (reg_t) RS1 <<
                                                   ", x" << std::dec << insn.rs2() << " = 0x" << std::hex << (reg_t) RS2 <<
                                                   ", x" << std::dec << insn.rs3() << " = 0x" << std::hex << (reg_t) RS3 <<
                                                   " /* X_NUM_RS == " << std::dec << x_num_rs <<
                                                   " */ ) = 0x" << std::hex << result << " -> x" << std::dec << insn.rd() << std::endl;
    return result;
  };

  // Semantics of CUS_CNOP: Compressed CV-X-IF NOP.
  reg_t cvxif_cus_cnop(insn_t insn)
  {
    std::cerr << "### [SPIKE] cvxif_cus_cnop(x" << std::dec << insn.rvc_rs1() << " = 0x" << std::hex << (reg_t) RVC_RS1 <<
                                          ", x" << std::dec << insn.rvc_rs2() << " = 0x" << std::hex << (reg_t) RVC_RS2 <<
                                          ") = 0xIGNORE" << std::endl;
    // Value will be ignored by writeback checker.
    return (reg_t) -1;
  };

  // Semantics of CUS_CADD: Compressed CV-X-IF ADD.
  reg_t cvxif_cus_cadd(insn_t insn)
  {
    reg_t result = (reg_t) sext_xlen((sreg_t) RVC_RS1 + (sreg_t) RVC_RS2);
    std::cerr << "### [SPIKE] cvxif_cus_cadd(x" << std::dec << insn.rvc_rs1() << " = 0x" << std::hex << (reg_t) RVC_RS1 <<
                                          ", x" << std::dec << insn.rvc_rs2() << " = 0x" << std::hex << (reg_t) RVC_RS2 <<
                                          ") = 0x" << std::hex << result << " -> x" << std::dec << insn.rvc_rd() << std::endl;
    return result;
  }

  // Extension constructor
  //TODO FIXME: May need checking of active ISA extensions since CV-X-IF extension conflicts with 'F' opcodes,
  cvxif_t()
  {
  }

  void raise_exception(insn_t insn, reg_t exc_index)
  {
    switch (exc_index) {
      case CAUSE_MISALIGNED_FETCH:
        throw trap_instruction_address_misaligned((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_FETCH_ACCESS:
        throw trap_instruction_access_fault((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_BREAKPOINT:
        throw trap_breakpoint((p ? p->get_state()->v : false), 1);
      case CAUSE_MISALIGNED_LOAD:
        // Use 0x1 as perfectly unaligned address;-)
        throw trap_load_address_misaligned((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_LOAD_ACCESS:
        // Use 0x1 as invalid address.
        throw trap_load_access_fault((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_MISALIGNED_STORE:
        // Use 0x1 as perfectly unaligned address;-)
        throw trap_store_address_misaligned((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_STORE_ACCESS:
        // Use 0x1 as invalid address.
        throw trap_store_access_fault((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_USER_ECALL:
        throw trap_user_ecall();
      case CAUSE_SUPERVISOR_ECALL:
        throw trap_supervisor_ecall();
      case CAUSE_VIRTUAL_SUPERVISOR_ECALL:
        throw trap_virtual_supervisor_ecall();
      case CAUSE_MACHINE_ECALL:
        throw trap_machine_ecall();
      case CAUSE_FETCH_PAGE_FAULT:
        throw trap_instruction_page_fault((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_LOAD_PAGE_FAULT:
        // Use 0x1 as always-faulting address.
        throw trap_load_page_fault((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_STORE_PAGE_FAULT:
        // Use 0x1 as always-faulting address.
        throw trap_store_page_fault((p ? p->get_state()->v : false), 1, 0, 0);
      case CAUSE_FETCH_GUEST_PAGE_FAULT:
        throw trap_instruction_guest_page_fault(0, 0, 0);
      case CAUSE_LOAD_GUEST_PAGE_FAULT:
        throw trap_load_guest_page_fault(0, 0, 0);
      case CAUSE_VIRTUAL_INSTRUCTION:
        throw trap_virtual_instruction(0);
      case CAUSE_STORE_GUEST_PAGE_FAULT:
        throw trap_store_guest_page_fault(0, 0, 0);
      default:
        throw trap_unknown_instruction(exc_index, (reg_t)0);
    }
  }

  // Define templates of new instructions.
  customX(0)
  customX(1)
  customX(2)
  customX(3)

  // CV-X-IF non-custom3 32-bit insns
  cvxif_insn_32(cus_add_rs3_madd)
  cvxif_insn_32(cus_add_rs3_msub)
  cvxif_insn_32(cus_add_rs3_nmadd)
  cvxif_insn_32(cus_add_rs3_nmsub)
  // FIXME FORNOW Consider CUS_ADD_RS3_RTYPE is an R-type insn.
  // This may change if/when CVA6 supports selectable
  // R-type/R4-type three-source-reg insns.
  cvxif_insn_32(cus_add_rs3_rtype)

  // CV-X-IF non-custom 16-bit insns
  cvxif_insn_16(cus_cnop)
  cvxif_insn_16(cus_cadd)

  void reset()
  {
    std::cerr << "[Extension '" << name() << "'] reset()" << std::endl;

    // Obtain the XLEN of the resetting processor.
    xlen = p->get_xlen();

    // Attempt to extract Spike parameter 'cvxif_x_num_rs' which indicates the number
    // of source register ports supported in the current target.  Legal values are 2 and 3.
    // Try core-specific setting first; if not present, try global default.
    // If the parameter is not set (parameter query returns 0) or is not legal, default to 3.
    x_num_rs = 3;

    if (proc) {  // Proceed only if Processor pointer was explicitly initialized.
      openhw::Params params = proc->get_params();
      uint64_t num_rs = 0;
      bool got_value = true;   // Be optimistic.
      if (params.exist("/top/core/" + std::to_string(proc->get_id()) + "/", "cvxif_x_num_rs"))
        // Core-specific setting present
        num_rs = params["/top/core/" + std::to_string(proc->get_id()) + "/" + "cvxif_x_num_rs"].a_uint64_t;
      else if (params.exist("/top/cores/", "cvxif_x_num_rs"))
        // No core-specific setting present, try global default.
        num_rs = params["/top/cores/cvxif_x_num_rs"].a_uint64_t;
      else
        got_value = false;

      if (got_value) {
        if (num_rs >=2 && num_rs <= 3) {
          std::cerr << "[SPIKE] Setting X_NUM_RS to value " << num_rs << std::endl;
          x_num_rs = num_rs;
        }
        else
          std::cerr << "[SPIKE] Invalid X_NUM_RS value!" << std::endl;
      }
      else
        std::cerr << "[SPIKE] No parameter for X_NUM_RS!" << std::endl;
    }
  }

  // Set instruction handlers for CV-X-IF opcode patterns.
  // NOTE: This method may need revisiting if multiple custom extensions are to be loaded
  //       simultaneously in the future.
  std::vector<insn_desc_t> get_instructions()
  {
// Factor out tedious, repetitive code as all combinations of RV32/RV64 x RVI/RVE x fast/logged
// simulation path use the same handler functions.
// Leave a differentiating 'default' value at the "RV64E logged" entry to help with debugging.
#define ADD_INSN_TO_DECODER(match,mask,impl, dflt) \
    insns.push_back((insn_desc_t){(match), (mask), &impl, &impl, &impl, &impl, &impl, &impl, &impl, &dflt})

    std::vector<insn_desc_t> insns;
    ADD_INSN_TO_DECODER(0x0b, 0x7f, ::illegal_instruction, c0);
    ADD_INSN_TO_DECODER(0x2b, 0x7f, ::illegal_instruction, c1);
    ADD_INSN_TO_DECODER(0x5b, 0x7f, ::illegal_instruction, c2);
    ADD_INSN_TO_DECODER(0x7b, 0x7f, c3,                    c3);

    // Instructions ADD_RS3_*
    ADD_INSN_TO_DECODER(MATCH_CVXIF_CUS_ADD_RS3_MADD,  MASK_CVXIF_CUS_ADD_RS3_MADD,  cvxif_32_cus_add_rs3_madd,  cvxif_32_cus_add_rs3_madd);
    ADD_INSN_TO_DECODER(MATCH_CVXIF_CUS_ADD_RS3_MSUB,  MASK_CVXIF_CUS_ADD_RS3_MSUB,  cvxif_32_cus_add_rs3_msub,  cvxif_32_cus_add_rs3_msub);
    ADD_INSN_TO_DECODER(MATCH_CVXIF_CUS_ADD_RS3_NMADD, MASK_CVXIF_CUS_ADD_RS3_NMADD, cvxif_32_cus_add_rs3_nmadd, cvxif_32_cus_add_rs3_nmadd);
    ADD_INSN_TO_DECODER(MATCH_CVXIF_CUS_ADD_RS3_NMSUB, MASK_CVXIF_CUS_ADD_RS3_NMSUB, cvxif_32_cus_add_rs3_nmsub, cvxif_32_cus_add_rs3_nmsub);
    ADD_INSN_TO_DECODER(MATCH_CVXIF_CUS_ADD_RS3_RTYPE, MASK_CVXIF_CUS_ADD_RS3_RTYPE, cvxif_32_cus_add_rs3_rtype, cvxif_32_cus_add_rs3_rtype);

    // Compressed insns CNOP/CADD.
    ADD_INSN_TO_DECODER(MATCH_CVXIF_CUS_CNOP,          MASK_CVXIF_CUS_CNOP,           cvxif_16_cus_cnop,          cvxif_16_cus_cnop);
    ADD_INSN_TO_DECODER(MATCH_CVXIF_CUS_CADD,          MASK_CVXIF_CUS_CADD,           cvxif_16_cus_cadd,          cvxif_16_cus_cadd);
    return insns;
  }

private:
  // State variables go here.
  uint64_t x_num_rs = 0;
  int xlen = 0;
};

REGISTER_EXTENSION(cvxif, []() { std::cerr << "### [SPIKE] registering extension 'cvxif' ==> create new instance!" << std::endl; return new cvxif_t; })
