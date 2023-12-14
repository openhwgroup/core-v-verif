// Copyright 2023 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Oystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Design Name:    cv32e40s_rchk_shim                                         //
// Project Name:   CV32E40S                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Module keeps track of which OBI response should carry a    //
//                 legal rchk value and which do not. Scrambles rchk for      //
//                 non-integrity regions as defined by PMA_CFG.               //
////////////////////////////////////////////////////////////////////////////////

module uvmt_cv32e40s_rchk_shim import cv32e40s_pkg::*;
#(  parameter int unsigned  MAX_OUTSTANDING              = 2,
    parameter int           PMA_NUM_REGIONS              = 0,
    parameter pma_cfg_t     PMA_CFG[PMA_NUM_REGIONS-1:0] = '{default:PMA_R_DEFAULT},
    parameter logic [31:0]  DM_REGION_START              = 32'hF0000000,
    parameter logic [31:0]  DM_REGION_END                = 32'hF0003FFF,
    parameter logic         GENERATE_VALID_RCHK          = 0
 )
(
  input  logic        clk,
  input  logic        rst_n,

  // OBI address phase handshake
  input  logic        req_i,
  input  logic        gnt_i,
  input  logic        dbg_i,
  input  logic [31:0] addr_i,

  // OBI response phase signals
  input  logic [31:0] rdata_i,
  input  logic        rvalid_i,
  input  logic        err_i,
  input  logic [4:0]  rchk_i,    // From outside

  // rchk output
  output logic [4:0]  rchk_o     // to cv32e40s

);

  localparam OUTSTND_CNT_WIDTH = $clog2(MAX_OUTSTANDING+1);


  // FIFO is 1 bit deeper than the maximum value of bus_cnt_i
  // Index 0 is tied low to enable direct use of bus_cnt_i to pick correct FIFO index.
  logic [MAX_OUTSTANDING:0] fifo_q;
  logic req_has_integrity;
  logic resp_has_integrity;

  // Outstanding counter signals
  logic [OUTSTND_CNT_WIDTH-1:0] cnt_q;                        // Transaction counter
  logic [OUTSTND_CNT_WIDTH-1:0] next_cnt;                     // Next value for cnt_q
  logic                         count_up;
  logic                         count_down;

  // PMA lookup
  pma_cfg_t    pma_cfg;
  logic [31:0] word_addr;

  // Check for access to DM_REGION in debug mode
  logic        dm_access_debug;

  assign dm_access_debug = (addr_i >= DM_REGION_START) && (addr_i <= DM_REGION_END) && dbg_i;

  /////////////////////////////////////////////////////////////
  // Outstanding transactions counter
  // Used for tracking the integrity attribute
  /////////////////////////////////////////////////////////////
  assign count_up = req_i && gnt_i;  // Increment upon accepted transfer request
  assign count_down = rvalid_i;      // Decrement upon accepted transfer response

  always_comb begin
    case ({count_up, count_down})
      2'b00 : begin
        next_cnt = cnt_q;
      end
      2'b01 : begin
        next_cnt = cnt_q - 1'b1;
      end
      2'b10 : begin
        next_cnt = cnt_q + 1'b1;
      end
      2'b11 : begin
        next_cnt = cnt_q;
      end
      default:;
    endcase
  end

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      cnt_q <= '0;
    end else begin
      cnt_q <= next_cnt;
    end
  end

  //////////////////////
  // Integrity tracking
  //////////////////////

  // PMA addresses are word addresses
  assign word_addr = {2'b00, addr_i[31:2]};

  generate
    if(PMA_NUM_REGIONS == 0) begin: no_pma

      always_comb begin
        // PMA is deconfigured, use NO_PMA_R_DEFAULT as default.
        pma_cfg = NO_PMA_R_DEFAULT;

        // Access to debug module in debug mode has no integrity
        req_has_integrity = dm_access_debug ? 1'b0 : pma_cfg.integrity;
      end

    end
    else begin: pma

      // Identify PMA region
      always_comb begin

        // If no match, use default PMA config as default.
        pma_cfg = PMA_R_DEFAULT;

        for(int i = PMA_NUM_REGIONS-1; i >= 0; i--)  begin
          if((word_addr >= PMA_CFG[i].word_addr_low) &&
             (word_addr <  PMA_CFG[i].word_addr_high)) begin
            pma_cfg = PMA_CFG[i];
          end
        end

        // Access to debug module in debug mode has no integrity
        req_has_integrity = dm_access_debug ? 1'b0 : pma_cfg.integrity;
      end
    end

  endgenerate

  // FIFO to keep track of which responses come from an integrity enabled region
  always_ff @ (posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      fifo_q <= '0;
    end
    else begin
      if (req_i && gnt_i) begin
        // Accepted address phase, populate FIFO with expected integrity
        fifo_q <= {fifo_q[MAX_OUTSTANDING-1:1], req_has_integrity, 1'b0};
      end
    end
  end

  assign resp_has_integrity = fifo_q[cnt_q];

  // Invert all rchk bits if response is from a non-integrity region, else
  // generate correct response
  always_comb begin
    if (GENERATE_VALID_RCHK == 1) begin
      rchk_o = resp_has_integrity ? {
        ^{err_i, 1'b0},
        ^{rdata_i[31:24]},
        ^{rdata_i[23:16]},
        ^{rdata_i[15:8]},
        ^{rdata_i[7:0]}
      } : ~{
        ^{err_i, 1'b0},
        ^{rdata_i[31:24]},
        ^{rdata_i[23:16]},
        ^{rdata_i[15:8]},
        ^{rdata_i[7:0]}
      };
    end else begin
      rchk_o = resp_has_integrity ? rchk_i : ~rchk_i;
    end
  end

endmodule : uvmt_cv32e40s_rchk_shim
