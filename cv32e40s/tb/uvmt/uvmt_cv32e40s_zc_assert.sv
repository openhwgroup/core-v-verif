//
// Copyright 2022 OpenHW Group
// Copyright 2022 Silicon Labs
//
// Licensed under the Solderpad Hardware Licence, Version 2.1 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

module uvmt_cv32e40s_zc_assert
  import uvm_pkg::*;
  import uvma_rvfi_pkg::*;
  import cv32e40s_pkg::*;
  (
      uvma_rvfi_instr_if_t rvfi,
      uvmt_cv32e40s_support_logic_module_o_if_t.slave_mp support_if
  );


  // ---------------------------------------------------------------------------
  // Local parameters
  // ---------------------------------------------------------------------------
`ifndef DSIM
  localparam PUSH_POP_INSTR_MASK      = 32'h FFFF_FF03;
  localparam PUSH_INSTR_REF           = 32'h 0000_B802;
  localparam POP_INSTR_REF            = 32'h 0000_BA02;
  localparam POPRET_INSTR_REF         = 32'h 0000_BE02;
  localparam POPRETZ_INSTR_REF        = 32'h 0000_BC02;

  localparam MVA_INSTR_MASK           = 32'h FFFF_FC63;
  localparam MVA01S_INSTR_REF         = 32'h 0000_AC62;
  localparam MVSA01_INSTR_REF         = 32'h 0000_AC22;
`else  // DSIM
  // As of DSIM version 20220822.0.0 or earlier, the DSIM User Guide reports
  // the following "known issue":
  //   Only variables, nets, expressions and event expressions can be passed as
  //   arguments to named sequences and properties. Arguments or local variables
  //   of type sequence or property are not yet supported.
  int PUSH_POP_INSTR_MASK      = 32'h FFFF_FF03;
  int PUSH_INSTR_REF           = 32'h 0000_B802;
  int POP_INSTR_REF            = 32'h 0000_BA02;
  int POPRET_INSTR_REF         = 32'h 0000_BE02;
  int POPRETZ_INSTR_REF        = 32'h 0000_BC02;

  int MVA_INSTR_MASK           = 32'h FFFF_FC63;
  int MVA01S_INSTR_REF         = 32'h 0000_AC62;
  int MVSA01_INSTR_REF         = 32'h 0000_AC22;
`endif // DSIM



  // ---------------------------------------------------------------------------
  // Local variables
  // ---------------------------------------------------------------------------
  string info_tag = "CV32E40S_ZC_ASSERT";


  // ---------------------------------------------------------------------------
  // Clocking blocks
  // ---------------------------------------------------------------------------

  // Single clock, single reset design, use default clocking
  default clocking @(posedge rvfi.clk); endclocking
  default disable iff !(rvfi.reset_n);


  // ---------------------------------------
  // Assertions
  // ---------------------------------------

  // Asserting that when a suboperation causes an exception,
  // no subsequent suboperation of the instruction causes
  // any activity on the data bus
  property p_multiop_exception_stop_dbus(logic[31:0] ins_mask, logic[31:0] ins_ref);
    (rvfi.rvfi_valid && rvfi.rvfi_trap[0] && rvfi.match_instr(ins_ref, ins_mask))
    |->
    support_if.req_after_exception == 0;

  endproperty

  a_multiop_exception_stop_dbus_push : assert property(p_multiop_exception_stop_dbus(PUSH_POP_INSTR_MASK, PUSH_INSTR_REF))
        else `uvm_error(info_tag, "Activity on dbus after exception during push instruction");

  a_multiop_exception_stop_dbus_pop  : assert property(p_multiop_exception_stop_dbus(PUSH_POP_INSTR_MASK, POP_INSTR_REF))
        else `uvm_error(info_tag, "Activity on dbus after exception during pop instruction");

  a_multiop_exception_stop_dbus_popretz : assert property(p_multiop_exception_stop_dbus(PUSH_POP_INSTR_MASK, POPRETZ_INSTR_REF))
        else `uvm_error(info_tag, "Activity on dbus after exception during popretz instruction");

  a_multiop_exception_stop_dbus_popret : assert property(p_multiop_exception_stop_dbus(PUSH_POP_INSTR_MASK, POPRET_INSTR_REF))
        else `uvm_error(info_tag, "Activity on dbus after exception during popret instruction");

  a_multiop_exception_stop_dbus_mvsa01 : assert property(p_multiop_exception_stop_dbus(MVA_INSTR_MASK, MVSA01_INSTR_REF))
        else `uvm_error(info_tag, "Activity on dbus after exception during mvsa01 instruction");

  a_multiop_exception_stop_dbus_mva01s : assert property(p_multiop_exception_stop_dbus(MVA_INSTR_MASK, MVA01S_INSTR_REF))
        else `uvm_error(info_tag, "Activity on dbus after exception during mva01s instruction");



endmodule : uvmt_cv32e40s_zc_assert
