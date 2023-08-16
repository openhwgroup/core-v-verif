// Copyright 2023 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


module uvmt_cv32e40s_xsecure_interface_integrity_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;
  #(
    parameter int       SECURE   = 1,
    parameter int       ALBUF_DEPTH = 3,
    parameter int       ALBUF_CNT_WIDTH = 2
  )
  (
    //Interfaces:
    uvmt_cv32e40s_support_logic_module_o_if_t.slave_mp support_if,

    //Signals:
    input rst_ni,
    input clk_i,

    //Alert:
    input logic alert_major,
    input logic alert_major_due_to_integrity_err,

    //CSR:
    input logic integrity_enabled,
    input logic nmip,
    input logic [10:0] mcause_exception_code,


    //OBI data:
    input obi_data_req_t obi_data_req_packet,
    input obi_data_resp_t obi_data_resp_packet,
    input logic [31:0] obi_data_addr,
    input logic obi_data_req,
    input logic obi_data_reqpar,
    input logic obi_data_gnt,
    input logic obi_data_gntpar,
    input logic obi_data_rvalid,
    input logic obi_data_rvalidpar,

    //OBI instr:
    input obi_inst_req_t obi_instr_req_packet,
    input obi_inst_resp_t obi_instr_resp_packet,
    input logic [31:0] obi_instr_addr,
    input logic obi_instr_req,
    input logic obi_instr_reqpar,
    input logic obi_instr_gnt,
    input logic obi_instr_gntpar,
    input logic obi_instr_rvalid,
    input logic obi_instr_rvalidpar,

    //Register file memory:
    input logic [REGFILE_WORD_WIDTH-1:0] gpr_mem [CORE_PARAM_REGFILE_NUM_WORDS],
    input logic rf_we,
    input logic [4:0] rf_waddr,
    input logic [31:0] rf_wdata,

    //Alignment buffer:
    input inst_resp_t alb_resp_i,
    input inst_resp_t [ALBUF_DEPTH-1:0] alb_resp_q,
    input logic [ALBUF_DEPTH-1:0] alb_valid,
    input logic [ALBUF_CNT_WIDTH-1:0] alb_wptr,
    input logic [ALBUF_CNT_WIDTH-1:0] alb_rptr1,
    input logic [ALBUF_CNT_WIDTH-1:0] alb_rptr2,

    //If:
    input logic if_valid,
    input logic if_instr_integrity_err,
    input logic if_instr_cmpr,
    input logic [31:0] if_instr_pc,
    input logic dummy_insert,

    //Id:
    input logic id_ready,
    input logic id_instr_integrity_err,
    input logic id_abort_op,
    input logic id_illegal_insn,

    //Wb:
    input logic wb_valid,
    input logic wb_integrity_err,
    input logic [6:0] wb_instr_opcode,
    input logic wb_exception,
    input logic [10:0] wb_exception_code,
    input logic data_integrity_err,

    //MISC:
    input logic [$bits(ctrl_state_e)-1:0] ctrl_fsm_cs,
    input logic [$bits(pc_mux_e)-1:0] pc_mux,
    input logic pc_set,
    input logic seq_valid,
    input logic kill_if,
    input logic [1:0] n_flush_q,
    input logic rchk_err_instr,
    input logic rchk_err_data
  );


  // Default settings:
  default clocking @(posedge clk_i); endclocking
  default disable iff (!(rst_ni) || !(SECURE));
  string info_tag = "CV32E40S_XSECURE_ASSERT_COVERPOINTS";
  string info_tag_glitch = "CV32E40S_XSECURE_ASSERT_COVERPOINTS (GLITCH BEHAVIOR)";
  string info_tag_rtl_bug = "CV32E40S_XSECURE_ASSERT_COVERPOINTS (RTL BUG)";

  // Local parameters:
  localparam ASSUMED_VALUE_BE = 4'b1111;
  localparam ASSUMED_VALUE_WE = 1'b0;
  localparam ASSUMED_VALUE_ATOP = 6'b00_0000;
  localparam ASSUMED_VALUE_WDATA = 32'h0000_0000;
  localparam ASSUMED_VALUE_EXOKAY = 1'b0;
  localparam ASSUMED_VALUE_MID = 8'h0;
  localparam REQ_WAS_READ = 1'b1;
  localparam DEBUG_TAKEN = 2'b11;

  localparam RCHK_STORE = 4;
  localparam ZERO = '0;

  localparam LSU_LOAD_INTEGRITY_FAULT = 11'h402;
  localparam LSU_STORE_INTEGRITY_FAULT = 11'h403;

  localparam int  OBI_DATA_RESP_ERR_BIT0_ERROR_FROM_BUS = 0;

    function logic [12:0] f_achk (logic [31:0] wdata, logic dbg, logic [5:0] atop,  logic [7:0] mid,  logic [3:0] be,  logic we,  logic [2:0] prot,  logic [1:0] memtype, logic [31:0] addr);
    f_achk = {
      ^wdata[31:24],
      ^wdata[23:16],
      ^wdata[15:8],
      ^wdata[7:0],
      ~^dbg,
      ^atop[5:0],
      ^mid[7:0],
      ~^{be[3:0], we},
      ~^{prot[2:0], memtype[1:0]},
      ^addr[31:24],
      ^addr[23:16],
      ^addr[15:8],
      ^addr[7:0]};
  endfunction


  function logic [4:0] f_rchk (logic err, logic exokay, logic [31:0] rdata);
    f_rchk = {
      ^{err, exokay},
      ^rdata[31:24],
      ^rdata[23:16],
      ^rdata[15:8],
      ^rdata[7:0]};
  endfunction



  logic [12:0] achk_data_calculated;
  logic [12:0] achk_instr_calculated;
  logic [4:0] rchk_instr_calculated;
  logic [4:0] rchk_data_calculated;

  //Independent generation of the checksum based on the outputted data

  assign achk_data_calculated = f_achk(
    obi_data_req_packet.wdata,
    obi_data_req_packet.dbg,
    ASSUMED_VALUE_ATOP,
    ASSUMED_VALUE_MID,
    obi_data_req_packet.be,
    obi_data_req_packet.we,
    obi_data_req_packet.prot,
    obi_data_req_packet.memtype,
    obi_data_addr);

  assign achk_instr_calculated = f_achk(
    ASSUMED_VALUE_WDATA,
    obi_instr_req_packet.dbg,
    ASSUMED_VALUE_ATOP,
    ASSUMED_VALUE_MID,
    ASSUMED_VALUE_BE,
    ASSUMED_VALUE_WE,
    obi_instr_req_packet.prot,
    obi_instr_req_packet.memtype,
    obi_instr_addr);

  assign rchk_instr_calculated = f_rchk(
    obi_instr_resp_packet.err,
    ASSUMED_VALUE_EXOKAY,
    obi_instr_resp_packet.rdata);

  assign rchk_data_calculated = f_rchk(
    obi_data_resp_packet.err[OBI_DATA_RESP_ERR_BIT0_ERROR_FROM_BUS],
    ASSUMED_VALUE_EXOKAY,
    obi_data_resp_packet.rdata);


  //Verify that interface integrity is enabled by default

  a_xsecure_integrity_default_on: assert property (
    $rose(rst_ni)
    |->
    integrity_enabled
  ) else `uvm_error(info_tag, "Interface integrity checking is not enabled when exiting reset.\n");


  //Verify that the parity signals are the complements of the non-parity signals at all times.

  property p_parity_signal_is_invers_of_signal(signal, parity_signal);
    @(posedge clk_i)
    parity_signal == ~signal;
  endproperty

  a_xsecure_integrity_data_req_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      obi_data_req,
      obi_data_reqpar)
  ) else `uvm_error(info_tag, "The OBI data bus request parity signal is not inverse of the request signal.\n");

    a_xsecure_integrity_instr_req_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      obi_instr_req,
      obi_instr_reqpar)
  ) else `uvm_error(info_tag, "The OBI instruction bus request parity signal is not inverse of the request signal.\n");

  a_xsecure_integrity_data_gnt_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      obi_data_gnt,
      obi_data_gntpar)
  ) else `uvm_error(info_tag, "The OBI data bus grant parity signal is not inverse of the grant signal.\n");

  a_xsecure_integrity_instr_gnt_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      obi_instr_gnt,
      obi_instr_gntpar)
  ) else `uvm_error(info_tag, "The OBI instruction bus grant parity signal is not inverse of the grant signal.\n");

  a_xsecure_integrity_data_rvalid_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      obi_data_rvalid,
      obi_data_rvalidpar)
  ) else `uvm_error(info_tag, "The OBI data bus rvalid parity signal is not inverse of the rvalid signal.\n");

  a_xsecure_integrity_instr_rvalid_parity: assert property (
    p_parity_signal_is_invers_of_signal(
      obi_instr_rvalid,
      obi_instr_rvalidpar)
  ) else `uvm_error(info_tag, "The OBI instruction bus rvalid parity signal is not inverse of the rvalid signal.\n");


  //Verify that the received and generated checksums are correct

  property p_checksum(req, chk_input, chk_calculated);
    if_valid //TODO: do we need this one?
    && req
    |->
    chk_input == chk_calculated;
  endproperty

  a_xsecure_integrity_data_achk: assert property (
    p_checksum(
      obi_data_req,
      obi_data_req_packet.achk,
      achk_data_calculated)
  ) else `uvm_error(info_tag, "The request checksum for the OBI data bus is not as expected.\n");


  a_xsecure_integrity_instr_achk: assert property (
    p_checksum(
      obi_instr_req,
      obi_instr_req_packet.achk,
      achk_instr_calculated)
  ) else `uvm_error(info_tag_rtl_bug, "The request checksum for the OBI instructions bus is not as expected.\n");


  a_xsecure_integrity_instr_rchk: assert property (
    obi_instr_rvalid
    |->
    obi_instr_resp_packet.rchk == rchk_instr_calculated
  );

  property p_checksum_data_rchk(memory_op, rvalid, chk_input, chk_calculated);
    memory_op
    && rvalid
    |->
    chk_input == chk_calculated;
  endproperty

  a_xsecure_integrity_store_data_rchk: assert property (
    p_checksum_data_rchk(
      support_if.req_was_store,
      obi_data_rvalid,
      obi_data_resp_packet.rchk[RCHK_STORE],
      rchk_data_calculated[RCHK_STORE])
  );


  a_xsecure_integrity_load_data_rchk: assert property (
    p_checksum_data_rchk(
    !support_if.req_was_store,
    obi_data_rvalid,
    obi_data_resp_packet.rchk,
    rchk_data_calculated)
  );


  //Verify that major alert and exception code "Instruction parity/checksum fault" are set when executing an instruction with an integrity error

  a_glitch_xsecure_integrity_instr_integrity_error: assert property (
    wb_valid
    && wb_integrity_err
    && ctrl_fsm_cs != DEBUG_TAKEN //When entering debug we dont trigger any exceptions
    |->
    wb_exception
    && (wb_exception_code == EXC_CAUSE_INSTR_INTEGRITY_FAULT
    || wb_exception_code == EXC_CAUSE_INSTR_FAULT) //Instruction fault exception have higher priority than integrity fault

    ##1 alert_major
  ) else `uvm_error(info_tag_glitch, "Attempted execution of an instruction with integrity error does set the major alert or correct exception code.\n");


  //Verify that major alert is set if the inputted parity signals dont correspond to the inputted non-parity signals

  property p_parity_fault(signal, parity_signal);
    parity_signal != ~signal
    |=>
    alert_major;
  endproperty


  a_glitch_xsecure_integrity_data_gnt_parity: assert property (
    p_parity_fault(
      obi_data_gnt,
      obi_data_gntpar)
  ) else `uvm_error(info_tag_glitch, "A OBI data bus grant parity fault does not set the major alert.\n");

  a_glitch_xsecure_integrity_instr_gnt_parity: assert property (
    p_parity_fault(
      obi_instr_gnt,
      obi_instr_gntpar)
  ) else `uvm_error(info_tag_glitch, "A OBI instruction bus grant parity fault does not set the major alert.\n");

  a_glitch_xsecure_integrity_data_rvalid_parity: assert property (
    p_parity_fault(
      obi_data_rvalid,
      obi_data_rvalidpar)
  ) else `uvm_error(info_tag_glitch, "A OBI data bus rvalid parity fault does not set the major alert.\n");

  a_glitch_xsecure_integrity_instr_rvalid_parity: assert property (
    p_parity_fault(
      obi_instr_rvalid,
      obi_instr_rvalidpar)
  ) else `uvm_error(info_tag_glitch, "A OBI instruction bus rvalid parity fault does not set the major alert.\n");


  //Verify that major alert is set if the inputted checksums dont correspond to what the packets contains
  //But only if integrity checking is enabled

  sequence seq_checksum_fault(rvalid, req_had_integrity, memory_op, rchk_input, rchk_calculated);
    rvalid
    && req_had_integrity
    && memory_op
    && rchk_input != rchk_calculated;
  endsequence


  a_glitch_xsecure_integrity_rchk_instr_read: assert property (
    integrity_enabled

    ##0 seq_checksum_fault(
      obi_instr_rvalid,
      support_if.instr_req_had_integrity,
      REQ_WAS_READ,
      obi_instr_resp_packet.rchk,
      rchk_instr_calculated)

    |->
    alert_major_due_to_integrity_err
  ) else `uvm_error(info_tag_glitch, "An error in the OBI instruction bus's response packet's checksum does not set the major alert.\n");

  a_glitch_xsecure_integrity_rchk_data_store: assert property (
    integrity_enabled

    ##0 seq_checksum_fault(
      obi_data_rvalid,
      support_if.data_req_had_integrity,
      support_if.req_was_store,
      obi_data_resp_packet.rchk[RCHK_STORE],
      rchk_data_calculated[RCHK_STORE])

    |->
    alert_major_due_to_integrity_err
  ) else `uvm_error(info_tag_glitch, "An error in the OBI data bus's response packet's checksum does not set the major alert.\n");

  a_glitch_xsecure_integrity_rchk_data_read: assert property (
    integrity_enabled

    ##0 seq_checksum_fault(
      obi_data_rvalid,
      support_if.data_req_had_integrity,
      !support_if.req_was_store,
      obi_data_resp_packet.rchk,
      rchk_data_calculated)

    |->
    alert_major_due_to_integrity_err
  ) else `uvm_error(info_tag_glitch, "An error in the OBI data bus's response packet's checksum does not set the major alert.\n");


  //Verify that checksum errors for instructions and data do not set alert major if the integrity checking is disabled

  a_glitch_xsecure_integrity_rchk_instr_read_integrity_disabled: assert property (
    !integrity_enabled

    ##0 seq_checksum_fault(
      obi_instr_rvalid,
      support_if.instr_req_had_integrity,
      REQ_WAS_READ,
      obi_instr_resp_packet.rchk,
      rchk_instr_calculated)

    |->
    //No integrity errors have triggered major alert, or an integrity error has triggered major alert, but it is not due to rchk instr error
    !alert_major_due_to_integrity_err
    || (alert_major_due_to_integrity_err && !rchk_err_instr)

  ) else `uvm_error(info_tag_glitch, "An error in the OBI instruction bus's response packet's checksum sets the major alert even though interface integrity checking is disabled.\n");

  a_glitch_xsecure_integrity_rchk_data_store_integrity_disabled: assert property (
    !integrity_enabled

    ##0 seq_checksum_fault(
      obi_data_rvalid,
      support_if.data_req_had_integrity,
      support_if.req_was_store,
      obi_data_resp_packet.rchk[RCHK_STORE],
      rchk_data_calculated[RCHK_STORE])

    |->
    !alert_major_due_to_integrity_err
    || (alert_major_due_to_integrity_err && !rchk_err_data)
  ) else `uvm_error(info_tag_glitch, "An error in the OBI data bus's response packet's checksum sets the major alert even though interface integrity checking is disabled.\n");

  a_glitch_xsecure_integrity_rchk_data_read_integrity_disabled: assert property (
    !integrity_enabled

    ##0 seq_checksum_fault(
      obi_data_rvalid,
      support_if.data_req_had_integrity,
      !support_if.req_was_store,
      obi_data_resp_packet.rchk,
      rchk_data_calculated)

    |->
    !alert_major_due_to_integrity_err
    || (alert_major_due_to_integrity_err && !rchk_err_data)
  ) else `uvm_error(info_tag_glitch, "An error in the OBI data bus's response packet's checksum sets the major alert even though interface integrity checking is disabled.\n");


  //Verify that the register file is updated even though there is an integrity error

  a_xsecure_integrity_update_register_parity_checksum_error: assert property (
    rf_we
    && rf_waddr != ZERO
    |=>
    gpr_mem[$past(rf_waddr)][31:0] == $past(rf_wdata)
  ) else `uvm_error(info_tag_glitch, "The register file is not updated.\n");

  //Check that it is possible to write to the register file when there is an integrity error
  c_glitch_xsecure_integrity_update_register_parity_checksum_error: cover property (
    rf_we
    && rf_waddr != ZERO
    && obi_data_rvalid
    && data_integrity_err
  );


  //Verify that the integrity bits to the data and instructions fetched from the OBI bus are set if there are parity or checksum faults

  property p_parity_fault_integrity_err_gnt(rvalid, gnt_parity_err, integrity_err);
    rvalid
    && gnt_parity_err
    |->
    integrity_err;
  endproperty

  a_glitch_xsecure_integrity_instr_gntparity_fault_integrity_err: assert property (
    p_parity_fault_integrity_err_gnt(
      obi_instr_rvalid,
      support_if.gntpar_error_in_response_instr,
      if_instr_integrity_err)
  ) else `uvm_error(info_tag_glitch, "The integrity error bit is not set in the OBI instruction bus's response packet, even though there was grant parity error when generating the request packet.\n");

  a_glitch_xsecure_integrity_data_gntparity_fault_integrity_err: assert property (
    p_parity_fault_integrity_err_gnt(
      obi_data_rvalid,
      support_if.gntpar_error_in_response_data,
      data_integrity_err)
  ) else `uvm_error(info_tag_glitch, "The integrity error bit is not set in the OBI data bus's response packet, even though there was grant parity error when generating the request packet.\n");


  property p_parity_fault_integrity_err_rvalid(rvalid, parity_rvalid, integrity_err);
    rvalid
    && parity_rvalid != ~rvalid
    |->
    integrity_err;
  endproperty

  a_glitch_xsecure_integrity_instr_rvalidparity_fault_integrity_err: assert property (
    p_parity_fault_integrity_err_rvalid(
      obi_instr_rvalid,
      obi_instr_rvalidpar,
      if_instr_integrity_err)
  ) else `uvm_error(info_tag_glitch, "The integrity error bit is not set in the OBI instruction bus's response packet, even though there was a rvalid parity error.\n");

  a_glitch_xsecure_integrity_data_rvalidparity_fault_integrity_err: assert property (
    p_parity_fault_integrity_err_rvalid(
      obi_data_rvalid,
      obi_data_rvalidpar,
      data_integrity_err)
  ) else `uvm_error(info_tag_glitch, "The integrity error bit is not set in the OBI data bus's response packet, even though there was a rvalid parity error.\n");


  property p_rchk_fault_integrity_err(req_had_integrity, load_from_memory, rvalid, rchk_input, rchk_calculated, integrity_err);
    integrity_enabled
    && req_had_integrity
    && load_from_memory
    && rvalid
    && rchk_input != rchk_calculated
    |->
    integrity_err;
  endproperty

  a_glitch_xsecure_integrity_instr_rchk_fault_integrity_err: assert property (
    p_rchk_fault_integrity_err(
      support_if.instr_req_had_integrity,
      REQ_WAS_READ,
      obi_instr_rvalid,
      obi_instr_resp_packet.rchk,
      rchk_instr_calculated,
      if_instr_integrity_err)
  ) else `uvm_error(info_tag_glitch, "The integrity error bit is not set in the OBI instruction bus's response packet, even though there was a checksum error.\n");

  a_glitch_xsecure_integrity_data_rchk_fault_integrity_err_store: assert property (
    p_rchk_fault_integrity_err(
      support_if.data_req_had_integrity,
      support_if.req_was_store,
      obi_data_rvalid,
      obi_data_resp_packet.rchk[RCHK_STORE],
      rchk_data_calculated[RCHK_STORE],
      data_integrity_err)
  ) else `uvm_error(info_tag_glitch, "The integrity error bit is not set in the OBI data bus's response packet, even though there was a checksum error in the store operation.\n");

  a_glitch_xsecure_integrity_data_rchk_fault_integrity_err_load: assert property (
    p_rchk_fault_integrity_err(
      support_if.data_req_had_integrity,
      !support_if.req_was_store,
      obi_data_rvalid,
      obi_data_resp_packet.rchk,
      rchk_data_calculated,
      data_integrity_err)
  ) else `uvm_error(info_tag_glitch, "The integrity error bit is not set in the OBI data bus's response packet, even though there was a checksum error in the load operation.\n");


  //Verify that the integrity error bit and the checksum bits is forwarded into the alignement buffer together with the instruction

  property p_instr_to_alignment_buffer(wptr_position);
    obi_instr_rvalid
    && alb_wptr == wptr_position
    && !kill_if
    && n_flush_q == 0 //There is no outstanding request that needs to be disregarded (due to unpredicted PC jump)
    |=>
    alb_resp_q[wptr_position].bus_resp.rchk == $past(obi_instr_resp_packet.rchk)
    && alb_resp_q[wptr_position].bus_resp.integrity_err == $past(if_instr_integrity_err)
    && alb_resp_q[wptr_position].bus_resp.integrity == $past(support_if.instr_req_had_integrity);
  endproperty


  generate
    for (genvar wptr = 0; wptr < ALBUF_DEPTH; wptr++) begin

      a_xsecure_integrity_instr_to_alignment_buffer: assert property (
        p_instr_to_alignment_buffer(wptr)
      ) else `uvm_error(info_tag, "The integrity error bit and/or the checksum bits from a response packet is not forwarded into the alignment buffer\n");

      a_glitch_xsecure_integrity_instr_to_alignment_buffer: assert property (
        p_instr_to_alignment_buffer(wptr)
      ) else `uvm_error(info_tag_glitch, "The integrity error bit and/or the checksum bits from a response packet is not forwarded into the alignment buffer\n");

    end
  endgenerate


  //Verify that the instruction propegated to the id stage have an integrity error if any of its related instruction fetches have integrity errors or alignment buffer based checksum errors.

  logic is_obi_addr;

  logic was_pc_set;
  always_latch begin
    if(!clknrst_if.reset_n) begin

    end else if ($past(pc_set)) begin
      was_pc_set = 1'b1;
    end else if (if_instr_pc[31:2] != $past(if_instr_pc[31:2])) begin
      was_pc_set = 1'b0;
    end
  end

  assign is_obi_addr =
    !was_pc_set
    || (was_pc_set
    && (pc_mux != PC_BOOT
      && pc_mux != PC_MRET
      && pc_mux != PC_DRET
      && pc_mux != PC_TRAP_EXC
      && pc_mux != PC_TRAP_IRQ
      && pc_mux != PC_TRAP_DBD
      && pc_mux != PC_TRAP_DBE
      && pc_mux != PC_TRAP_NMI
      && pc_mux != PC_TRAP_CLICV
      && pc_mux != PC_POINTER
      && pc_mux != PC_TBLJUMP)
    );

  logic [4:0] alb_input_rchk_calculated;
  logic [4:0] alb_rptr1_rchk_calculated;
  logic [4:0] alb_rptr2_rchk_calculated;

  assign alb_input_rchk_calculated = f_rchk(alb_resp_i.bus_resp.err, ASSUMED_VALUE_EXOKAY, alb_resp_i.bus_resp.rdata);
  assign alb_rptr1_rchk_calculated = f_rchk(alb_resp_q[alb_rptr1].bus_resp.err, ASSUMED_VALUE_EXOKAY, alb_resp_q[alb_rptr1].bus_resp.rdata);
  assign alb_rptr2_rchk_calculated = f_rchk(alb_resp_q[alb_rptr2].bus_resp.err, ASSUMED_VALUE_EXOKAY, alb_resp_q[alb_rptr2].bus_resp.rdata);

  logic alb_input_integrity_err;
  logic alb_rptr1_integrity_err;
  logic alb_rptr2_integrity_err;

  assign alb_input_integrity_err = ((alb_resp_i.bus_resp.rchk != alb_input_rchk_calculated) && (obi_instr_rvalid && support_if.instr_req_had_integrity)) || alb_resp_i.bus_resp.integrity_err;
  assign alb_rptr1_integrity_err = ((alb_resp_q[alb_rptr1].bus_resp.rchk != alb_rptr1_rchk_calculated) && (alb_resp_q[alb_rptr1].mpu_status == MPU_OK) && alb_resp_q[alb_rptr1].bus_resp.integrity) || alb_resp_q[alb_rptr1].bus_resp.integrity_err;
  assign alb_rptr2_integrity_err = ((alb_resp_q[alb_rptr2].bus_resp.rchk != alb_rptr2_rchk_calculated) && (alb_resp_q[alb_rptr2].mpu_status == MPU_OK) && alb_resp_q[alb_rptr2].bus_resp.integrity) || alb_resp_q[alb_rptr2].bus_resp.integrity_err;

  logic if_instr_aligned;
  assign if_instr_aligned = (if_instr_pc[1:0] == '0);

  logic if_integrity_err_calculated;

  always_latch begin
    if(!alb_valid[alb_rptr1]) begin
      if_integrity_err_calculated = alb_input_integrity_err;
    end else if (alb_valid[alb_rptr1] && alb_valid[alb_rptr2]) begin
      if_integrity_err_calculated = (if_instr_aligned || if_instr_cmpr) ? alb_rptr1_integrity_err : alb_rptr1_integrity_err || alb_rptr2_integrity_err;
    end else if (alb_valid[alb_rptr1] && !alb_valid[alb_rptr2]) begin
      if_integrity_err_calculated = (if_instr_aligned || if_instr_cmpr) ? alb_rptr1_integrity_err : alb_rptr1_integrity_err || alb_input_integrity_err;
    end
  end

  a_glitch_xsecure_integrity_instr_fetch_fusion: assert property (
    if_valid
    && id_ready
    && integrity_enabled
    && is_obi_addr
    && !dummy_insert
    && !seq_valid

    //Assume no error:
    ##1 !id_abort_op
    && !id_illegal_insn
    |->
    id_instr_integrity_err == $past(if_integrity_err_calculated)
  );


  //Verify that integrity errors on the OBI data bus set mcause exception code to 1026 or 1027, and set alert major

  a_glitch_xsecure_integrity_data_integrity_err_helper_assert: assert property (

    obi_data_rvalid
    && data_integrity_err
    |=>
    $rose(nmip)
    || $past(nmip)

  ) else `uvm_error(info_tag_glitch, "An associated parity/checksum error does not set the pending NMI signal.\n");


  a_glitch_xsecure_integrity_data_integrity_err: assert property (

    obi_data_rvalid
    && data_integrity_err
    ##1 $rose(nmip)
    ##1 nmip[*0:$]
    ##1 !nmip //the nmi is handeled
    |->
    (mcause_exception_code == LSU_LOAD_INTEGRITY_FAULT || mcause_exception_code == LSU_STORE_INTEGRITY_FAULT)
    && alert_major

  ) else `uvm_error(info_tag_glitch, "The NMI caused by an associated parity/checksum error does not have exception code 1027 or 1026.\n");

  //Load instructions
  c_glitch_xsecure_security_parity_checksum_fault_NMI_load_instruction: cover property (

    obi_data_rvalid
    && data_integrity_err
    && wb_instr_opcode == OPCODE_LOAD
    ##1 $rose(nmip)
  );

  //Store instructions
  c_glitch_xsecure_security_parity_checksum_fault_NMI_store_instruction: cover property (

    obi_data_rvalid
    && data_integrity_err
    && wb_instr_opcode == OPCODE_STORE
    ##1 $rose(nmip)

  );

  endmodule : uvmt_cv32e40s_xsecure_interface_integrity_assert
