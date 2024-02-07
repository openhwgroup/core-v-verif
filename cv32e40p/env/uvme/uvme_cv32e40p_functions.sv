// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2023 Dolphin Design
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


`ifndef __UVME_CV32E40P_FUNCTIONS_SV__
`define __UVME_CV32E40P_FUNCTIONS_SV__

  function automatic logic [31:0] get_user_def_c_insn_if_true (input logic [31:0] insn);
    logic [31:0] i_insn = insn;
    
    case(i_insn[1:0])
      2'b00 : begin
                if (i_insn[15:13] == 3'b000 && i_insn[12:5] != 8'd0)                    i_insn = TB_USER_DEF_C_ADDI4SPN;
              end
      2'b01 : begin
                if (i_insn[15:13] == 3'b000 && i_insn[12:2] != 11'd0)                   i_insn = TB_USER_DEF_C_ADDI;
                if (i_insn[15:13] == 3'b010 && i_insn[11:7] != 5'd0)                    i_insn = TB_USER_DEF_C_LI;
                if (i_insn[15:13] == 3'b011 && {i_insn[12],i_insn[6:2]} != 6'd0) begin
                  if      (i_insn[11:7] == 5'd2)                                        i_insn = TB_USER_DEF_C_ADDI16SP;
                  else if (i_insn[11:7] != 5'd0)                                        i_insn = TB_USER_DEF_C_LUI;
                end
              end
      2'b10 : begin
                if (i_insn[15:13] == 3'b000 && i_insn[12] != 1'b1 && i_insn[11:7] != 5'd0)                        i_insn = TB_USER_DEF_C_SLLI;
                if (i_insn[15:13] == 3'b010 && i_insn[11:7] != 5'd0)                                              i_insn = TB_USER_DEF_C_LWSP;
                if (i_insn[15:13] == 3'b100 && i_insn[12] == 1'b0 && i_insn[11:7] != 5'd0 && i_insn[6:2] == 5'd0) i_insn = TB_USER_DEF_C_JR;
                if (i_insn[15:13] == 3'b100 && i_insn[12] == 1'b0 && i_insn[11:7] != 5'd0 && i_insn[6:2] != 5'd0) i_insn = TB_USER_DEF_C_MV;
                if (i_insn[15:13] == 3'b100 && i_insn[12] == 1'b1 && i_insn[11:7] != 5'd0 && i_insn[6:2] == 5'd0) i_insn = TB_USER_DEF_C_JALR;
                if (i_insn[15:13] == 3'b100 && i_insn[12] == 1'b1 && i_insn[11:7] != 5'd0 && i_insn[6:2] != 5'd0) i_insn = TB_USER_DEF_C_ADD;
              end
      2'b11 : begin /* do nothing */ end
    endcase

    return i_insn;
  endfunction : get_user_def_c_insn_if_true


`endif // __UVME_CV32E40P_FUNCTIONS_SV__
