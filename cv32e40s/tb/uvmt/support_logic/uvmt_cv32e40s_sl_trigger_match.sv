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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


module uvmt_cv32e40s_sl_trigger_match
  import uvmt_cv32e40s_base_test_pkg::*;
  (
    input logic clk_i,
    input logic rst_ni,
    output logic [CORE_PARAM_DBG_NUM_TRIGGERS-1:0] trigger_match_mem,
    output logic [CORE_PARAM_DBG_NUM_TRIGGERS-1:0] trigger_match_execute,
    output logic [CORE_PARAM_DBG_NUM_TRIGGERS-1:0] trigger_match_exception,
    output logic [CORE_PARAM_DBG_NUM_TRIGGERS-1:0] is_trigger_match
  );

  localparam TDATA1_RESET = 32'h2800_1000;
  localparam TDATA1_ET_M_MODE = 9;
  localparam TDATA1_ET_U_MODE = 6;
  localparam TDATA1_LSB_TYPE = 28;
  localparam TDATA1_MSB_TYPE = 31;
  localparam TDATA1_LOAD = 0;
  localparam TDATA1_STORE = 1;
  localparam TDATA1_EXECUTE = 2;
  localparam TDATA1_M2_M6_U_MODE = 3;
  localparam TDATA1_M2_M6_M_MODE = 6;
  localparam TDATA1_LSB_MATCH = 7;
  localparam TDATA1_MSB_MATCH = 10;
  localparam TDATA1_MATCH_WHEN_EQUAL = 0;
  localparam TDATA1_MATCH_WHEN_GREATER_OR_EQUAL = 2;
  localparam TDATA1_MATCH_WHEN_LESSER = 3;

  localparam MAX_MEM_ACCESS = 13; //Push and pop can do 13 memory access. XIF can potentially do more (TODO (xif): check this when merging to cv32e40x)


  // signals to keep track of the conditions for triggering.
  logic [CORE_PARAM_DBG_NUM_TRIGGERS-1:0] system_conditions;
  logic [CORE_PARAM_DBG_NUM_TRIGGERS-1:0] csr_conditions_m2_m6;
  logic [CORE_PARAM_DBG_NUM_TRIGGERS-1:0] csr_conditions_etrigger;

  // keep track of what obi memory transactions that seems to trigger
  logic [MAX_MEM_ACCESS:0][CORE_PARAM_DBG_NUM_TRIGGERS-1:0] trigger_match_mem_op;

  // check if there are execute or exception trigger matches.
  logic execute_exception_trigger_match;


  generate

    assign system_conditions = rvfi.rvfi_valid && !rvfi.rvfi_dbg_mode;

    for (genvar t = 0; t < CORE_PARAM_DBG_NUM_TRIGGERS; t++) begin

      assign csr_conditions_m2_m6[t] =
        (in_support_if.tdata1_array[t][TDATA1_MSB_TYPE:TDATA1_LSB_TYPE] == 2 ||
        in_support_if.tdata1_array[t][TDATA1_MSB_TYPE:TDATA1_LSB_TYPE] == 6) &&
        ((rvfi.is_mmode && in_support_if.tdata1_array[t][TDATA1_M2_M6_M_MODE]) ||
        (rvfi.is_umode && in_support_if.tdata1_array[t][TDATA1_M2_M6_U_MODE]));


      assign csr_conditions_etrigger[t] =
        (in_support_if.tdata1_array[t][TDATA1_MSB_TYPE:TDATA1_LSB_TYPE] == 5) &&
        ((rvfi.is_mmode && in_support_if.tdata1_array[t][TDATA1_ET_M_MODE]) ||
        (rvfi.is_umode && in_support_if.tdata1_array[t][TDATA1_ET_U_MODE]));


        // Trigger match instruction:
      assign trigger_match_execute[t] = csr_conditions_m2_m6[t]
        && in_support_if.tdata1_array[t][TDATA1_EXECUTE]
        && system_conditions
        && !rvfi.rvfi_trap.clicptr //TODO: KD: burde finne ut hvorfor clicptr er et unntak.
        && (((rvfi.rvfi_pc_rdata == in_support_if.tdata2_array[t]) && in_support_if.tdata1_array[t][TDATA1_MSB_MATCH:TDATA1_LSB_MATCH] == TDATA1_MATCH_WHEN_EQUAL)
        || ((rvfi.rvfi_pc_rdata >= in_support_if.tdata2_array[t]) && in_support_if.tdata1_array[t][TDATA1_MSB_MATCH:TDATA1_LSB_MATCH] == TDATA1_MATCH_WHEN_GREATER_OR_EQUAL)
        || ((rvfi.rvfi_pc_rdata < in_support_if.tdata2_array[t]) && in_support_if.tdata1_array[t][TDATA1_MSB_MATCH:TDATA1_LSB_MATCH] == TDATA1_MATCH_WHEN_LESSER));

      // Trigger match exception:
      assign trigger_match_exception[t] = system_conditions
        && !trigger_match_execute
        && csr_conditions_etrigger[t]
        && rvfi.rvfi_trap.exception
        && in_support_if.tdata2_array[t][rvfi.rvfi_trap.exception_cause[$clog2(32)-1:0]];

    end
  endgenerate


  // Trigger match load and store:

  generate
    for (genvar mem_op = 0; mem_op < 13; mem_op++) begin : trigger_match_memory_operation
      uvmt_cv32e40s_sl_trigger_match_mem
      #(
        .MEMORY_OPERATION_NR (mem_op)
      )
      sl_trigger_match_mem
      (
        .clk_i (in_support_if.clk),
        .rst_ni (in_support_if.rst_n),
        .csr_conditions_m2_m6 (csr_conditions_m2_m6),
        .tdata1_array (in_support_if.tdata1_array),
        .tdata2_array (in_support_if.tdata2_array),
        .trigger_match_execute (trigger_match_execute),
        .trigger_match_mem (trigger_match_mem_op[mem_op])
      );
    end : trigger_match_memory_operation
  endgenerate


  assign execute_exception_trigger_match = (|trigger_match_execute) || (|trigger_match_exception);

  always_comb begin
    if (trigger_match_mem_op[0] && !execute_exception_trigger_match) begin
      trigger_match_mem = trigger_match_mem_op[0];

    end else if (trigger_match_mem_op[1] && !execute_exception_trigger_match) begin
      trigger_match_mem = trigger_match_mem_op[1];

    end else if (trigger_match_mem_op[2] && !execute_exception_trigger_match) begin
      trigger_match_mem = trigger_match_mem_op[2];

    end else if (trigger_match_mem_op[3] && !execute_exception_trigger_match) begin
      trigger_match_mem = trigger_match_mem_op[3];

    end else if (trigger_match_mem_op[4] && !execute_exception_trigger_match) begin
      trigger_match_mem = trigger_match_mem_op[4];

    end else if (trigger_match_mem_op[5] && !execute_exception_trigger_match) begin
      trigger_match_mem = trigger_match_mem_op[5];

    end else if (trigger_match_mem_op[6] && !execute_exception_trigger_match) begin
      trigger_match_mem = trigger_match_mem_op[6];

    end else if (trigger_match_mem_op[7] && !execute_exception_trigger_match) begin
      trigger_match_mem = trigger_match_mem_op[7];

    end else if (trigger_match_mem_op[8] && !execute_exception_trigger_match) begin
      trigger_match_mem = trigger_match_mem_op[8];

    end else if (trigger_match_mem_op[9] && !execute_exception_trigger_match) begin
      trigger_match_mem = trigger_match_mem_op[9];

    end else if (trigger_match_mem_op[10] && !execute_exception_trigger_match) begin
      trigger_match_mem = trigger_match_mem_op[10];

    end else if (trigger_match_mem_op[11] && !execute_exception_trigger_match) begin
      trigger_match_mem = trigger_match_mem_op[11];

    end else if (trigger_match_mem_op[12] && !execute_exception_trigger_match) begin
      trigger_match_mem = trigger_match_mem_op[12];

    end else begin
      trigger_match_mem = '0;
    end
  end


  assign is_trigger_match = trigger_match_mem | trigger_match_execute | trigger_match_exception;


endmodule
