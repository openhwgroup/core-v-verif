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
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

/*

This is a configurable FIFO.
It inputs item_in when add_item is set.
It always outputs the "oldest" fifo item.
It shifts the fifo on the next clock cycle when shift_fifo is set.

The figure shows how the FIFO behaves:

t1:               |  t2:               |  t3:               |
add_item          |  add_item          |  !add_item         |
&& !shift_fifo    |  && !shift_fifo    |  && !shift_fifo    |
_____________     |  _____________     |  _____________     |
|   |   |   |     |  |   |   |   |     |  |   |   |   |     |
|   |   | X |     |  | i1|   | X |     |  | i1| i2| X |     |
|___|___|___|     |  |___|___|___|     |  |___|___|___|     |
  ^                        ^                        ^
t4:               |  t5:               |  t6:               |
!add_item         |  !add_item         |  !add_item         |
&& shift_fifo     |  && shift_fifo     |  && !shift_fifo    |
_____________     |  _____________     |  _____________     |
|   |   |   |     |  |   |   |   |     |  |   |   |   |     |
| i1| i2| X |     |  | i2|   | X |     |  |   |   | X |     |
|___|___|___|     |  |___|___|___|     |  |___|___|___|     |
          ^                ^                ^
t7:               |  t8:               |  t9:               |
add_item          |  add_item          |  !add_item         |
&& !shift_fifo    |  && shift_fifo     |  && !shift_fifo    |
_____________     |  _____________     |  _____________     |
|   |   |   |     |  |   |   |   |     |  |   |   |   |     |
|   |   | X |     |  | i3|   | X |     |  | i4|   | X |     |
|___|___|___|     |  |___|___|___|     |  |___|___|___|     |
  ^                        ^                    ^
*/

module uvmt_cv32e40s_sl_fifo
  import cv32e40s_pkg::*;
  #(
    parameter type FIFO_TYPE_T = obi_inst_req_t,
    parameter FIFO_SIZE = 2
  )
  (
    input logic rst_ni,
    input logic clk_i,

    input logic add_item,
    input logic shift_fifo,

    input FIFO_TYPE_T item_in,
    output FIFO_TYPE_T item_out
  );

  // Extend the FIFO with one elemet to make sure the pointer will not underflow
  localparam FIFO_PTR_SIZE = $clog2(FIFO_SIZE+1);

  // Extend the FIFO with one elemet to make sure the pointer will not underflow
  FIFO_TYPE_T [FIFO_SIZE:0] fifo;
  logic [FIFO_PTR_SIZE-1:0] ptr;
  FIFO_TYPE_T zero;

  assign item_out = fifo[FIFO_SIZE];

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if(!rst_ni) begin
      fifo <= '0;
      ptr <= FIFO_SIZE;
      zero <= '0;
    end else begin
      if (add_item && !shift_fifo) begin
        fifo[ptr] <= item_in;
        ptr <= ptr - 1'b1;

      end else if (!add_item && shift_fifo) begin
        ptr <= ptr + 1'b1;

        fifo[FIFO_SIZE:1] <= fifo[FIFO_SIZE-1:0];
        fifo[0] <= zero;

      // If used correctly the fifo should not shift unless there already is an item in the fifo.
      // For safety we add this as a requirement for entering this fifo state.
      end else if (add_item && shift_fifo && ptr < FIFO_SIZE) begin
        fifo[FIFO_SIZE:1] <= fifo[FIFO_SIZE-1:0];
        fifo[0] <= zero;

        fifo[ptr+1'b1] <= item_in;
      end
    end
  end


endmodule : uvmt_cv32e40s_sl_fifo
