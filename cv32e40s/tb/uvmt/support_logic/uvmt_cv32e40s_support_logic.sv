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

module uvmt_cv32e40s_support_logic
  import uvm_pkg::*;
  import uvma_rvfi_pkg::*;
  import cv32e40s_pkg::*;
  import uvmt_cv32e40s_pkg::*;
  import uvma_rvfi_pkg::*;
  import isa_decoder_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;
  (
    uvma_rvfi_instr_if_t rvfi,
    uvmt_cv32e40s_support_logic_module_i_if_t.driver_mp in_support_if,
    uvmt_cv32e40s_support_logic_module_o_if_t.master_mp out_support_if,
    uvma_obi_memory_if_t data_obi_if,
    uvma_obi_memory_if_t instr_obi_if
  );


  // ---------------------------------------------------------------------------
  // Default Resolutions
  // ---------------------------------------------------------------------------

  default clocking @(posedge in_support_if.clk); endclocking
  default disable iff (!in_support_if.rst_n);

  // ---------------------------------------------------------------------------
  // Local parameters
  // ---------------------------------------------------------------------------

  localparam MAX_NUM_OUTSTANDING_OBI_REQUESTS = 2;

  // ---------------------------------------------------------------------------
  // Local variables
  // ---------------------------------------------------------------------------

  // Signal indicates an exception is active for a multiop instruction,
  // in other words a subop has triggered an exception. WB stage timing.
  logic exception_active;

  // Signal indicates data bus address phase completed last cycle
  logic data_bus_gnt_q;

  // flag for signaling first debug instruction
  logic first_debug_ins_flag;
  // prev rvfi_valid was a dret
  logic ins_was_dret;
  // flopped value of core control signal fetch_enable
  logic fetch_enable_q;
  // counter for keeping track of the number of rvfi_valids that have passed since the last observed debug_req
  int   req_vs_valid_cnt;


  obi_data_req_t data_obi_req;
  assign data_obi_req.addr      = data_obi_if.addr;
  assign data_obi_req.we        = data_obi_if.we;
  assign data_obi_req.be        = data_obi_if.be;
  assign data_obi_req.wdata     = data_obi_if.wdata;
  assign data_obi_req.memtype   = data_obi_if.memtype;
  assign data_obi_req.prot      = data_obi_if.prot;
  assign data_obi_req.dbg       = data_obi_if.dbg;
  assign data_obi_req.achk      = data_obi_if.achk;
  assign data_obi_req.integrity = '0;

  obi_inst_req_t instr_obi_req;
  assign instr_obi_req.addr      = instr_obi_if.addr;
  assign instr_obi_req.memtype   = instr_obi_if.memtype;
  assign instr_obi_req.prot      = instr_obi_if.prot;
  assign instr_obi_req.dbg       = instr_obi_if.dbg;
  assign instr_obi_req.achk      = instr_obi_if.achk;
  assign instr_obi_req.integrity = '0;

  // ---------------------------------------------------------------------------
  // Support logic blocks
  // ---------------------------------------------------------------------------

  // Decoder:
  always_comb begin
    out_support_if.asm_if = decode_instr(in_support_if.if_instr);
  end
  always_comb begin
    out_support_if.asm_id = decode_instr(in_support_if.id_instr);
  end
  always_comb begin
    out_support_if.asm_ex = decode_instr(in_support_if.ex_instr);
  end
  always_comb begin
    out_support_if.asm_wb = decode_instr(in_support_if.wb_instr);
  end
  always_comb begin
    out_support_if.asm_rvfi = decode_instr(rvfi.rvfi_insn);
  end


  // Check if a new obi data req arrives after an exception is triggered.
  // Used to verify exception timing with multiop instruction
  always @(posedge in_support_if.clk or negedge in_support_if.rst_n) begin
    if (!in_support_if.rst_n) begin
      out_support_if.req_after_exception <= 0;
      exception_active <= 0;
      data_bus_gnt_q <= 0;
    end else  begin
      // set prev bus gnt
      data_bus_gnt_q <= in_support_if.data_bus_gnt;

      // is a trap taken in WB?
      if (in_support_if.ctrl_fsm_o.pc_set && (in_support_if.ctrl_fsm_o.pc_mux == PC_TRAP_DBE || in_support_if.ctrl_fsm_o.pc_mux == PC_TRAP_EXC)) begin
        if (in_support_if.data_bus_req && data_bus_gnt_q) begin
          out_support_if.req_after_exception <= 1;
        end
        exception_active <= 1;
      end else if (rvfi.rvfi_valid) begin
        exception_active <= 0;
        out_support_if.req_after_exception <= 0;

      end else if (exception_active && data_bus_gnt_q && in_support_if.data_bus_req) begin
        out_support_if.req_after_exception <= 1;
      end
    end

  end //always

   // Detect first instruction of debug code
  assign out_support_if.first_debug_ins = rvfi.rvfi_valid && rvfi.rvfi_dbg_mode && !first_debug_ins_flag;


  always@ (posedge in_support_if.clk or negedge in_support_if.rst_n) begin
      if( !in_support_if.rst_n) begin
          first_debug_ins_flag <= 0;
          ins_was_dret <= 0;
      end else begin
          if(rvfi.rvfi_valid) begin
              if(rvfi.rvfi_dbg_mode) begin
                  first_debug_ins_flag <= 1;
              end else begin
                  first_debug_ins_flag <= 0;
              end
              if(rvfi.is_dret && !rvfi.rvfi_trap.trap) begin
                  ins_was_dret <= 1;
              end
          end
          if(ins_was_dret) begin
              first_debug_ins_flag <= 0;
              ins_was_dret <= 0;
          end
      end
  end


  //detect core startup
  assign out_support_if.first_fetch = in_support_if.fetch_enable && !fetch_enable_q;

  always@ (posedge in_support_if.clk or negedge in_support_if.rst_n) begin
      if( !in_support_if.rst_n) begin
          fetch_enable_q <= 0;
      end else if (in_support_if.fetch_enable) begin
          fetch_enable_q <= 1;
      end
  end

  //record a debug_req long enough that it could be taken
  always@ (posedge in_support_if.clk or negedge in_support_if.rst_n) begin
      if( !in_support_if.rst_n) begin
          out_support_if.recorded_dbg_req <= 0;
          req_vs_valid_cnt <= 4'h0;
      end else begin
          if(rvfi.rvfi_valid) begin
              if(in_support_if.debug_req_i) begin
                  out_support_if.recorded_dbg_req <= 1;
                  req_vs_valid_cnt <= 4'h1;
              end else if (req_vs_valid_cnt > 0) begin
                  req_vs_valid_cnt <= req_vs_valid_cnt - 1;
              end else begin
                  out_support_if.recorded_dbg_req <= 0;
              end
          end else if (in_support_if.debug_req_i) begin
                  out_support_if.recorded_dbg_req <= 1;
                  req_vs_valid_cnt <= 4'h2;
          end
      end
  end

if (CORE_PARAM_DBG_NUM_TRIGGERS == 0) begin
  assign trigger_match_mem = '0;
  assign trigger_match_execute = '0;
  assign trigger_match_exception = '0;
  assign is_trigger_match = '0;

end else begin

  uvmt_cv32e40s_sl_trigger_match
  sl_trigger_match
  (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),
    .trigger_match_mem (out_support_if.trigger_match_mem[CORE_PARAM_DBG_NUM_TRIGGERS-1:0]),
    .trigger_match_execute (out_support_if.trigger_match_execute[CORE_PARAM_DBG_NUM_TRIGGERS-1:0]),
    .trigger_match_exception (out_support_if.trigger_match_exception[CORE_PARAM_DBG_NUM_TRIGGERS-1:0]),
    .is_trigger_match (out_support_if.is_trigger_match[CORE_PARAM_DBG_NUM_TRIGGERS-1:0])
  );

  assign out_support_if.trigger_match_mem[CORE_PARAM_DBG_NUM_TRIGGERS] = 1'b0;
  assign out_support_if.trigger_match_execute[CORE_PARAM_DBG_NUM_TRIGGERS] = 1'b0;
  assign out_support_if.trigger_match_exception[CORE_PARAM_DBG_NUM_TRIGGERS] = 1'b0;
  assign out_support_if.is_trigger_match[CORE_PARAM_DBG_NUM_TRIGGERS] = 1'b0;

end



  // Count "irq_ack"

  always_latch begin
    if (in_support_if.rst_n == 0) begin
      out_support_if.cnt_irq_ack = 0;
    end else if (in_support_if.irq_ack) begin
      if ($past(out_support_if.cnt_irq_ack) != '1) begin
        out_support_if.cnt_irq_ack = $past(out_support_if.cnt_irq_ack) + 1;
      end
    end
  end


  // Count rvfi reported interrupts

  logic  do_count_rvfi_irq;
  always_comb begin
    do_count_rvfi_irq =
      rvfi.rvfi_intr.interrupt  &&
      !(rvfi.rvfi_intr.cause inside {[1024:1027]})  &&
      rvfi.rvfi_valid  &&
      ($past(out_support_if.cnt_rvfi_irqs) != '1);
  end

  always_latch begin
    if (in_support_if.rst_n == 0) begin
      out_support_if.cnt_rvfi_irqs = 0;
    end else if (do_count_rvfi_irq) begin
      out_support_if.cnt_rvfi_irqs = $past(out_support_if.cnt_rvfi_irqs) + 1;
    end
  end



  // ---------------------------------------------------------------------------
  // Support logic submodules
  // ---------------------------------------------------------------------------


  // Support logic for obi interfaces:

  //obi data bus:
  uvmt_cv32e40s_sl_obi_phases_monitor data_bus_obi_phases_monitor (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .obi_req (in_support_if.data_bus_req),
    .obi_gnt (in_support_if.data_bus_gnt),
    .obi_rvalid (in_support_if.data_bus_rvalid),

    .addr_ph_cont (out_support_if.data_bus_addr_ph_cont),
    .resp_ph_cont (out_support_if.data_bus_resp_ph_cont),
    .v_addr_ph_cnt (out_support_if.data_bus_v_addr_ph_cnt)
  );

  //obi instr bus:
  uvmt_cv32e40s_sl_obi_phases_monitor instr_bus_obi_phases_monitor (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .obi_req (in_support_if.instr_bus_req),
    .obi_gnt (in_support_if.instr_bus_gnt),
    .obi_rvalid (in_support_if.instr_bus_rvalid),

    .addr_ph_cont (out_support_if.instr_bus_addr_ph_cont),
    .resp_ph_cont (out_support_if.instr_bus_resp_ph_cont),
    .v_addr_ph_cnt (out_support_if.instr_bus_v_addr_ph_cnt)
  );

  //obi protocol between alignmentbuffer (ab) and instructoin (i) interface (i) mpu (m) (=> abiim)
  uvmt_cv32e40s_sl_obi_phases_monitor abiim_bus_obi_phases_monitor (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .obi_req (in_support_if.abiim_bus_req),
    .obi_gnt (in_support_if.abiim_bus_gnt),
    .obi_rvalid (in_support_if.abiim_bus_rvalid),

    .addr_ph_cont (out_support_if.abiim_bus_addr_ph_cont),
    .resp_ph_cont (out_support_if.alignment_buff_resp_ph_cont),
    .v_addr_ph_cnt (out_support_if.alignment_buff_addr_ph_cnt)
  );

  //obi protocol between LSU (l) MPU (m) and LSU (l) (=> lml)
  uvmt_cv32e40s_sl_obi_phases_monitor lml_bus_obi_phases_monitor (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .obi_req (in_support_if.lml_bus_req),
    .obi_gnt (in_support_if.lml_bus_gnt),
    .obi_rvalid (in_support_if.lml_bus_rvalid),

    .addr_ph_cont (out_support_if.lml_bus_addr_ph_cont),
    .resp_ph_cont (out_support_if.lsu_resp_ph_cont),
    .v_addr_ph_cnt (out_support_if.lsu_addr_ph_cnt)
  );


  //The submodule instances under will tell if the
  //the response's request had integrity

  uvmt_cv32e40s_sl_fifo
  #(
    .FIFO_TYPE_T (logic),
    .FIFO_SIZE (MAX_NUM_OUTSTANDING_OBI_REQUESTS)
  ) instr_req_had_integrity_i
  (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .add_item   (in_support_if.instr_bus_gnt && in_support_if.instr_bus_req),
    .shift_fifo (in_support_if.instr_bus_rvalid),

    .item_in    (in_support_if.req_instr_integrity),
    .item_out   (out_support_if.instr_req_had_integrity)
  );

  uvmt_cv32e40s_sl_fifo
  #(
    .FIFO_TYPE_T (logic),
    .FIFO_SIZE (MAX_NUM_OUTSTANDING_OBI_REQUESTS)
  ) data_req_had_integrity_i
  (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .add_item   (in_support_if.data_bus_gnt && in_support_if.data_bus_req),
    .shift_fifo (in_support_if.data_bus_rvalid),

    .item_in    (in_support_if.req_data_integrity),
    .item_out   (out_support_if.data_req_had_integrity)
  );

  uvmt_cv32e40s_sl_fifo
  #(
    .FIFO_TYPE_T (obi_data_req_t),
    .FIFO_SIZE (MAX_NUM_OUTSTANDING_OBI_REQUESTS)
  ) fifo_obi_data_req
  (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .add_item   (data_obi_if.gnt && data_obi_if.req),
    .shift_fifo (data_obi_if.rvalid),

    .item_in    (data_obi_req),
    .item_out   (out_support_if.obi_data_packet.req)
  );

  assign out_support_if.obi_data_packet.resp.rdata         = data_obi_if.rdata;
  assign out_support_if.obi_data_packet.resp.err           = data_obi_if.err;
  assign out_support_if.obi_data_packet.resp.rchk          = data_obi_if.rchk;
  assign out_support_if.obi_data_packet.resp.integrity_err = '0;
  assign out_support_if.obi_data_packet.resp.integrity     = '0;
  assign out_support_if.obi_data_packet.valid              = data_obi_if.rvalid;


  uvmt_cv32e40s_sl_fifo
  #(
    .FIFO_TYPE_T (obi_inst_req_t),
    .FIFO_SIZE (MAX_NUM_OUTSTANDING_OBI_REQUESTS)
  ) fifo_obi_instr_req
  (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .add_item   (instr_obi_if.gnt && instr_obi_if.req),
    .shift_fifo (instr_obi_if.rvalid),

    .item_in    (instr_obi_req),
    .item_out   (out_support_if.obi_instr_packet.req)
  );

  assign out_support_if.obi_instr_packet.resp.rdata         = instr_obi_if.rdata;
  assign out_support_if.obi_instr_packet.resp.err           = instr_obi_if.err;
  assign out_support_if.obi_instr_packet.resp.rchk          = instr_obi_if.rchk;
  assign out_support_if.obi_instr_packet.resp.integrity_err = '0;
  assign out_support_if.obi_instr_packet.resp.integrity     = '0;
  assign out_support_if.obi_instr_packet.valid              = instr_obi_if.rvalid;


  //The submodule instance under will tell if the
  //the response's request had a gntpar error
  //in the transfere of instructions on the OBI instruction bus.

  logic instr_gntpar_error;
  logic instr_prev_gntpar_error;
  logic data_gntpar_error;
  logic data_prev_gntpar_error;

  assign instr_gntpar_error = ((in_support_if.instr_bus_gnt == in_support_if.instr_bus_gntpar || instr_prev_gntpar_error) && in_support_if.instr_bus_req) && in_support_if.rst_n;
  assign data_gntpar_error = ((in_support_if.data_bus_gnt == in_support_if.data_bus_gntpar || data_prev_gntpar_error) && in_support_if.data_bus_req) && in_support_if.rst_n;

  always @(posedge in_support_if.clk, negedge in_support_if.rst_n) begin
    if(!in_support_if.rst_n) begin
      instr_prev_gntpar_error <= 1'b0;
      data_prev_gntpar_error <= 1'b0;
    end else begin

      if (in_support_if.instr_bus_req && !in_support_if.instr_bus_gnt) begin
        instr_prev_gntpar_error <= instr_gntpar_error;
      end else begin
        instr_prev_gntpar_error <= 1'b0;
      end

      if (in_support_if.data_bus_req && !in_support_if.data_bus_gnt) begin
        data_prev_gntpar_error <= data_gntpar_error;
      end else begin
        data_prev_gntpar_error <= 1'b0;
      end

    end
  end

  uvmt_cv32e40s_sl_fifo
  #(
    .FIFO_TYPE_T (logic),
    .FIFO_SIZE (MAX_NUM_OUTSTANDING_OBI_REQUESTS)
  ) sl_req_gntpar_error_in_resp_instr_i
  (
    .clk_i  (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .add_item   (in_support_if.instr_bus_gnt && in_support_if.instr_bus_req),
    .shift_fifo (in_support_if.instr_bus_rvalid),

    .item_in    (instr_gntpar_error),
    .item_out   (out_support_if.gntpar_error_in_response_instr)
  );

  //The submodule instance under will tell if the
  //the response's request had a gntpar error
  //in the transfere of data on the OBI data bus.

  uvmt_cv32e40s_sl_fifo
  #(
    .FIFO_TYPE_T (logic),
    .FIFO_SIZE (MAX_NUM_OUTSTANDING_OBI_REQUESTS)
  ) sl_req_gntpar_error_in_resp_data_i
  (
    .clk_i  (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .add_item   (in_support_if.data_bus_gnt && in_support_if.data_bus_req),
    .shift_fifo (in_support_if.data_bus_rvalid),

    .item_in    (data_gntpar_error),
    .item_out   (out_support_if.gntpar_error_in_response_data)
  );

endmodule : uvmt_cv32e40s_support_logic
