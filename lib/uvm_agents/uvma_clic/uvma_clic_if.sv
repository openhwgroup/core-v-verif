// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2022 Silicon Labs, Inc.
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


`ifndef __UVMA_CLIC_IF_SV__
`define __UVMA_CLIC_IF_SV__


/**
 * Encapsulates all signals and clocking of Interrupt interface. Used by
 * monitor and driver.
 */
interface uvma_clic_if_t#(CLIC_ID_WIDTH = 5);

    // ---------------------------------------------------------------------------
    // Interface wires
    // ---------------------------------------------------------------------------
    wire        clk;
    wire        reset_n;

    wire                        clic_irq;
    wire [CLIC_ID_WIDTH-1:0]    clic_irq_id;
    wire [7:0]                  clic_irq_level;
    wire [1:0]                  clic_irq_priv;
    wire                        clic_irq_shv;
    wire                        irq_ack;
    wire [31:0]                 irq;
    wire [4:0]                  irq_id;

    // // Used to time true clic entry with tracer instruction retirement
    wire        deferint;
    wire        ovp_cpu_state_stepi;

    // -------------------------------------------------------------------
    // Testbench control
    // ---------------------------------------------------------------------------
    // -------------------------------------------------------------------
    bit         is_active;  // Set to active drive the clic lines
    bit         is_mmode_irq_only;
    bit [31:0]  irq_drv;    // TB clic driver

    bit                       clic_irq_drv;
    bit [CLIC_ID_WIDTH-1:0]   clic_irq_id_drv;
    bit [1:0]                 clic_irq_priv_drv;
    bit [7:0]                 clic_irq_level_drv;
    bit                       clic_irq_shv_drv;

    bit [1:0]                 clic_irq_priv_masked;

    // typedef to be able to parameterize clic_irq_id_drv assignments
    // without warnings
    typedef bit [$bits(clic_irq_id_drv) - 1:0] clic_irq_id_t;

    // -------------------------------------------------------------------
    // Begin module code
    // -------------------------------------------------------------------

    // Mux in driver to irq lines
    //always_comb begin
    //  clic_irq = is_active ? clic_irq_drv : 1'b0;
    //end
    assign clic_irq       = is_active ? clic_irq_drv          : 1'b0;
    assign clic_irq_id    = is_active ? clic_irq_id_drv       : clic_irq_id_t'('b0);
    assign clic_irq_level = is_active ? clic_irq_level_drv    : 2'b0;
    assign clic_irq_priv  = is_active ? clic_irq_priv_masked  : 2'b11;
    assign clic_irq_shv   = is_active ? clic_irq_shv_drv      : 1'b0;

    assign clic_irq_priv_masked = is_mmode_irq_only ? 2'b11 : clic_irq_priv_drv;

    `ifndef FORMAL // suppress warning, initial is not supported in formal
    initial begin
        is_active = 1'b0;
        clic_irq_drv = '0;
    end
    `endif

    /**
        * Used by target DUT.
    */
    clocking dut_cb @(posedge clk or reset_n);
    endclocking : dut_cb

    /**
       * Used by uvma_clic_drv_c.
    */
    clocking drv_cb @(posedge clk or reset_n);
        input #1step irq_ack;
        output       irq_drv,
                     clic_irq_drv,
                     clic_irq_id_drv,
                     clic_irq_level_drv,
                     clic_irq_priv_drv,
                     clic_irq_shv_drv;
    endclocking : drv_cb

    /**
        * Used by uvma_clic_mon_c.
    */
    clocking mon_cb @(posedge clk or reset_n);
        input #1step irq_ack,
                     irq_drv,
                     clic_irq_drv,
                     clic_irq_id_drv,
                     clic_irq_level_drv,
                     clic_irq_priv_drv,
                     clic_irq_shv_drv;
    endclocking : mon_cb

    modport dut_mp    (clocking dut_cb);
    modport active_mp (clocking drv_cb);
    modport passive_mp(clocking mon_cb);

endinterface : uvma_clic_if_t


`endif // __UVMA_CLIC_IF_SV__
