//
// Copyright 2023 Silicon Labs Inc.
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


`ifndef __UVMA_WFE_WU_IF_SV__
`define __UVMA_WFE_WU_IF_SV__


/**
 * Encapsulates all signals of the wfe wakeup interface. Used by monitor
 * (uvma_wfe_wu_mon_c) and driver (uvma_wfe_wu_drv_c).
 */
interface uvma_wfe_wu_if_t ();

   import uvm_pkg::*;

    // Signals
    logic clk;
    logic reset_n;

    bit   is_active;
    bit   wfe_wu;

    `ifndef FORMAL
    initial begin
      is_active = 1'b0;
      wfe_wu    = 1'b0;
    end
    `endif
    /**
        * Used by target DUT.
    */
    clocking dut_cb @(posedge clk or reset_n);
    endclocking : dut_cb

    /**
       * Used by uvma_wfe_wu_drv_c.
    */
    clocking drv_cb @(posedge clk or reset_n);
      output       wfe_wu;
    endclocking : drv_cb

    /**
        * Used by uvma_wfe_wu_mon_c.
    */
    clocking mon_cb @(posedge clk or reset_n);
      input #1step wfe_wu;
    endclocking : mon_cb

    modport dut_mp    (clocking dut_cb);
    modport active_mp (clocking drv_cb);
    modport passive_mp(clocking mon_cb);

endinterface : uvma_wfe_wu_if_t


`endif // __UVMA_WFE_WU_IF_SV__
