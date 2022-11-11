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
    uvmt_cv32e40s_support_logic_if.master support_if
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


    // ---------------------------------------------------------------------------
    // Support logic blocks
    // ---------------------------------------------------------------------------


    // Check if a new obi data req arrives after an exception is triggered.
    // Used to verify exception timing with multiop instruction
    always @(posedge support_if.clk_i or negedge support_if.rst_ni) begin
      if (!support_if.rst_ni) begin
        support_if.req_after_exception_o <= 0;
        exception_active <= 0;
        data_bus_gnt_q <= 0;
      end else  begin
        // set prev bus gnt
        data_bus_gnt_q <= support_if.data_bus_gnt_i;

        // is a trap taken in WB?
        if (support_if.ctrl_fsm_o_i.pc_set && (support_if.ctrl_fsm_o_i.pc_mux == PC_TRAP_DBE || support_if.ctrl_fsm_o_i.pc_mux == PC_TRAP_EXC)) begin
          if (support_if.data_bus_req_i && data_bus_gnt_q) begin
            support_if.req_after_exception_o <= 1;
          end
          exception_active <= 1;
        end else if (rvfi.rvfi_valid) begin
          exception_active <= 0;
          support_if.req_after_exception_o <= 0;

        end else if (exception_active && data_bus_gnt_q && support_if.data_bus_req_i) begin
          support_if.req_after_exception_o <= 1;
        end



      end

    end //always



endmodule : uvmt_cv32e40s_support_logic


module uvmt_cv32e40s_obi_phases_monitor
  import uvm_pkg::*;
  (
    input logic clk_i,
    input logic rst_ni,

    input logic obi_req,
    input logic obi_gnt,
    input logic obi_rvalid,


    // continued address and respons phase indicators, indicates address and respons phases
    // of more than one cycle
    output logic addr_ph_cont,
    output logic resp_ph_cont,

    // address phase counter, used to verify no response phase preceedes an address phase
    output integer v_addr_ph_cnt
  );

  logic addr_ph_valid;
  logic rsp_ph_valid;
  logic obi_rready;

  assign obi_rready = 1'b1; //This is an assumption

  assign addr_ph_valid = obi_req == 1'b1 && obi_gnt == 1'b1;
  assign rsp_ph_valid = obi_rready == 1'b1 && obi_rvalid == 1'b1;


  always @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      addr_ph_cont <= 1'b0;
    end
    else begin
      if (obi_req == 1'b1 && obi_gnt == 1'b0) begin
        addr_ph_cont <= 1'b1;
      end
      else begin
        addr_ph_cont <= 1'b0;
      end
    end
  end

  always @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      resp_ph_cont <= 1'b0;
    end
    else begin
      if (obi_rvalid == 1'b1 && obi_rready == 1'b0) begin
        resp_ph_cont <= 1'b1;
      end
      else begin
        resp_ph_cont <= 1'b0;
      end
    end
  end

  always @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      v_addr_ph_cnt <= '0;
    end
    else begin
      if (addr_ph_valid && !rsp_ph_valid) begin
        v_addr_ph_cnt <= v_addr_ph_cnt + 1'b1;
      end
      else if (!addr_ph_valid && rsp_ph_valid && v_addr_ph_cnt > 0) begin
        v_addr_ph_cnt <= v_addr_ph_cnt - 1'b1;
      end
    end
  end
endmodule : uvmt_cv32e40s_obi_phases_monitor
