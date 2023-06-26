// Copyright 2023 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//


module uvmt_cv32e40s_sl_trigger_match_mem
  import uvmt_cv32e40s_base_test_pkg::*;
  #(
    parameter int MEMORY_OPERATION_NR = 0
  )
  (
    input logic clk_i,
    input logic rst_ni,
    input logic [CORE_PARAM_DBG_NUM_TRIGGERS-1:0] csr_conditions_m2_m6,
    input logic [31:0] tdata1_array[CORE_PARAM_DBG_NUM_TRIGGERS+1],
    input logic [31:0] tdata2_array[CORE_PARAM_DBG_NUM_TRIGGERS+1],
    input logic [CORE_PARAM_DBG_NUM_TRIGGERS-1:0] trigger_match_execute,
    output logic [CORE_PARAM_DBG_NUM_TRIGGERS-1:0] trigger_match_mem
  );

  localparam TDATA1_LOAD = 0;
  localparam TDATA1_STORE = 1;
  localparam TDATA1_LSB_MATCH = 7;
  localparam TDATA1_MSB_MATCH = 10;
  localparam TDATA1_MATCH_WHEN_EQUAL = 0;
  localparam TDATA1_MATCH_WHEN_GREATER_OR_EQUAL = 2;
  localparam TDATA1_MATCH_WHEN_LESSER = 3;

  localparam MAX_MEM_ACCESS = 13; //Push and pop can do 13 memory access. XIF can potentially do more (TODO (xif): check this when merging to cv32e40x)


  logic [3:0][31:0] byte_addr;
  logic [3:0][CORE_PARAM_DBG_NUM_TRIGGERS-1:0] byte_match;
  logic [3:0] byte_match_overview;

  generate
    for (genvar b = 0; b < 4; b++) begin

      // Calculate the address of each byte
      assign byte_addr[b] = rvfi.rvfi_mem_addr[MEMORY_OPERATION_NR*32 +: 32] + b;

      // Check if the bytes trigger
      for (genvar t = 0; t < CORE_PARAM_DBG_NUM_TRIGGERS; t++) begin
        assign byte_match[b][t] =
          !rvfi.rvfi_trap.exception &&
          !trigger_match_execute &&
          csr_conditions_m2_m6[t] &&
          ((tdata1_array[t][TDATA1_LOAD] && rvfi.rvfi_mem_rmask_intended[MEMORY_OPERATION_NR*4+b]) ||
          (tdata1_array[t][TDATA1_STORE] && rvfi.rvfi_mem_wmask_intended[MEMORY_OPERATION_NR*4+b])) &&
          (((byte_addr[b] == tdata2_array[t]) && tdata1_array[t][TDATA1_MSB_MATCH:TDATA1_LSB_MATCH] == TDATA1_MATCH_WHEN_EQUAL) ||
          ((byte_addr[b] >= tdata2_array[t]) && tdata1_array[t][TDATA1_MSB_MATCH:TDATA1_LSB_MATCH] == TDATA1_MATCH_WHEN_GREATER_OR_EQUAL) ||
          ((byte_addr[b] < tdata2_array[t]) && tdata1_array[t][TDATA1_MSB_MATCH:TDATA1_LSB_MATCH] == TDATA1_MATCH_WHEN_LESSER));
      end
    end
  endgenerate


    assign byte_match_overview = {|byte_match[3], |byte_match[2], |byte_match[1], |byte_match[0]};

  always_comb begin
    // No byte triggers:
    if (byte_match_overview == 0) begin
      trigger_match_mem = '0;

    // Only byte zero matches
    end else if (!byte_match_overview[3] && !byte_match_overview[2] && !byte_match_overview[1] && byte_match_overview[0]) begin
      trigger_match_mem = byte_match[0];

    // Byte one matches, byte two and three dont match
    end else if (!byte_match_overview[3] && !byte_match_overview[2] && byte_match_overview[1]) begin
      if(byte_addr[1][31:2] == byte_addr[0][31:2]) begin
        trigger_match_mem = byte_match[1] | byte_match[0];
      end else if (byte_match[0]) begin
        trigger_match_mem = byte_match[0];
      end else begin
        trigger_match_mem = byte_match[1] | byte_match[0];
      end

    // Byte two matches, byte three dont match
    end else if (!byte_match_overview[3] && byte_match_overview[2]) begin
      if(byte_addr[2][31:2] == byte_addr[0][31:2]) begin
        trigger_match_mem = byte_match[2] | byte_match[1] | byte_match[0];
      end else if(byte_addr[1][31:2] == byte_addr[0][31:2] && (|byte_match[1] || |byte_match[0])) begin
        trigger_match_mem = byte_match[1] | byte_match[0];
      end else if (byte_match[0]) begin
        trigger_match_mem = byte_match[0];
      end else begin
        trigger_match_mem = byte_match[2] | byte_match[1] | byte_match[0];
      end

    // Byte three matches
    end else begin
      if(byte_addr[3][31:2] == byte_addr[0][31:2]) begin
        trigger_match_mem = byte_match[3] | byte_match[2] | byte_match[1] | byte_match[0];
      end else if(byte_addr[2][31:2] == byte_addr[0][31:2] && (|byte_match[2] || |byte_match[1] || |byte_match[0])) begin
        trigger_match_mem = byte_match[2] | byte_match[1] | byte_match[0];
      end else if(byte_addr[1][31:2] == byte_addr[0][31:2] && (|byte_match[1] || |byte_match[0])) begin
        trigger_match_mem = byte_match[1] | byte_match[0];
      end else if (byte_match[0]) begin
        trigger_match_mem = byte_match[0];
      end else begin
        trigger_match_mem = byte_match[3] | byte_match[2] | byte_match[1] | byte_match[0];
      end
    end
  end

endmodule : uvmt_cv32e40s_sl_trigger_match_mem
