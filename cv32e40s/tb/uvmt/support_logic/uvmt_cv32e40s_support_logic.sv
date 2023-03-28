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

module uvmt_cv32e40s_support_logic
  import uvm_pkg::*;
  import uvma_rvfi_pkg::*;
  import cv32e40s_pkg::*;
  (
    uvma_rvfi_instr_if rvfi,
    uvmt_cv32e40s_input_to_support_logic_module_if.driver_mp in_support_if,
    uvmt_cv32e40s_support_logic_for_assert_coverage_modules_if.master_mp out_support_if
  );

  // ---------------------------------------------------------------------------
  // Local parameters
  // ---------------------------------------------------------------------------



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


  // ---------------------------------------------------------------------------
  // Support logic blocks
  // ---------------------------------------------------------------------------


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
    .resp_ph_cont (out_support_if.abiim_bus_resp_ph_cont),
    .v_addr_ph_cnt (out_support_if.abiim_bus_v_addr_ph_cnt)
  );

  //obi protocol between LSU (l) MPU (m) and LSU (l) (=> lml)
  uvmt_cv32e40s_sl_obi_phases_monitor lml_bus_obi_phases_monitor (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .obi_req (in_support_if.lml_bus_req),
    .obi_gnt (in_support_if.lml_bus_gnt),
    .obi_rvalid (in_support_if.lml_bus_rvalid),

    .addr_ph_cont (out_support_if.lml_bus_addr_ph_cont),
    .resp_ph_cont (out_support_if.lml_bus_resp_ph_cont),
    .v_addr_ph_cnt (out_support_if.lml_bus_v_addr_ph_cnt)
  );

  //obi protocol between LSU (l) respons (r) filter (f) and the OBI (o) data (d) interface (i) (=> lrfodi)
  uvmt_cv32e40s_sl_obi_phases_monitor lrfodi_bus_obi_phases_monitor (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .obi_req (in_support_if.lrfodi_bus_req),
    .obi_gnt (in_support_if.lrfodi_bus_gnt),
    .obi_rvalid (in_support_if.lrfodi_bus_rvalid),

    .addr_ph_cont (out_support_if.lrfodi_bus_addr_ph_cont),
    .resp_ph_cont (out_support_if.lrfodi_bus_resp_ph_cont),
    .v_addr_ph_cnt (out_support_if.lrfodi_bus_v_addr_ph_cnt)
  );

  //The submodule instance under will tell if the
  //the response's request required a store operation.

  uvmt_cv32e40s_sl_req_attribute_fifo req_was_store_i
  (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .gnt (in_support_if.data_bus_gnt),
    .req (in_support_if.data_bus_req),
    .rvalid (in_support_if.data_bus_rvalid),
    .req_attribute_i (in_support_if.req_is_store & in_support_if.rst_n),

    .is_req_attribute_in_response_o (out_support_if.req_was_store)
  );

  //The submodule instance under will tell if the
  //the response's request had integrity
  //in the transfere of instructions on the OBI instruction bus.

  uvmt_cv32e40s_sl_req_attribute_fifo instr_req_had_integrity_i
  (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .gnt (in_support_if.instr_bus_gnt),
    .req (in_support_if.instr_bus_req),
    .rvalid (in_support_if.instr_bus_rvalid),
    .req_attribute_i (in_support_if.req_instr_integrity & in_support_if.rst_n),

    .is_req_attribute_in_response_o (out_support_if.instr_req_had_integrity)
  );

  //The submodule instance under will tell if the
  //the response's request had integrity
  //in the transfere of data on the OBI data bus.

  uvmt_cv32e40s_sl_req_attribute_fifo data_req_had_integrity_i
  (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .gnt (in_support_if.data_bus_gnt),
    .req (in_support_if.data_bus_req),
    .rvalid (in_support_if.data_bus_rvalid),
    .req_attribute_i (in_support_if.req_data_integrity & in_support_if.rst_n),

    .is_req_attribute_in_response_o (out_support_if.data_req_had_integrity)
  );

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

  uvmt_cv32e40s_sl_req_attribute_fifo sl_req_gntpar_error_in_resp_instr_i
  (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .gnt (in_support_if.instr_bus_gnt),
    .req (in_support_if.instr_bus_req),
    .rvalid (in_support_if.instr_bus_rvalid),
    .req_attribute_i (instr_gntpar_error),

    .is_req_attribute_in_response_o (out_support_if.gntpar_error_in_response_instr)
  );

  //The submodule instance under will tell if the
  //the response's request had a gntpar error
  //in the transfere of data on the OBI data bus.

  uvmt_cv32e40s_sl_req_attribute_fifo sl_req_gntpar_error_in_resp_data_i
  (
    .clk_i (in_support_if.clk),
    .rst_ni (in_support_if.rst_n),

    .gnt (in_support_if.data_bus_gnt),
    .req (in_support_if.data_bus_req),
    .rvalid (in_support_if.data_bus_rvalid),
    .req_attribute_i (data_gntpar_error),

    .is_req_attribute_in_response_o (out_support_if.gntpar_error_in_response_data)
  );

endmodule : uvmt_cv32e40s_support_logic

