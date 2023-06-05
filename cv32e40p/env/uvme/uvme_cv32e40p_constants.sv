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


`ifndef __UVME_CV32E40P_CONSTANTS_SV__
`define __UVME_CV32E40P_CONSTANTS_SV__


parameter uvme_cv32e40p_sys_default_clk_period   =  1_500; // 10ns
parameter uvme_cv32e40p_debug_default_clk_period = 10_000; // 10ns

// For RVFI/RVVI
parameter ILEN = 32;
parameter XLEN = 32;
parameter FLEN = 32;
parameter RVFI_NRET = 1;

// Control how often to print core scoreboard checked heartbeat messages
parameter PC_CHECKED_HEARTBEAT = 10_000;

// Map the virtual peripheral registers
parameter CV_VP_REGISTER_BASE          = 32'h0080_0000;
parameter CV_VP_REGISTER_SIZE          = 32'h0000_1000;

parameter CV_VP_VIRTUAL_PRINTER_OFFSET = 32'h0000_0000;
parameter CV_VP_RANDOM_NUM_OFFSET      = 32'h0000_0040;
parameter CV_VP_CYCLE_COUNTER_OFFSET   = 32'h0000_0080;
parameter CV_VP_STATUS_FLAGS_OFFSET    = 32'h0000_00c0;
parameter CV_VP_FENCEI_TAMPER_OFFSET   = 32'h0000_0100;
parameter CV_VP_INTR_TIMER_OFFSET      = 32'h0000_0140;
parameter CV_VP_DEBUG_CONTROL_OFFSET   = 32'h0000_0180;
parameter CV_VP_OBI_SLV_RESP_OFFSET    = 32'h0000_01c0;
parameter CV_VP_SIG_WRITER_OFFSET      = 32'h0000_0200;

parameter CV_VP_VIRTUAL_PRINTER_BASE   = CV_VP_REGISTER_BASE + CV_VP_VIRTUAL_PRINTER_OFFSET;
parameter CV_VP_RANDOM_NUM_BASE        = CV_VP_REGISTER_BASE + CV_VP_RANDOM_NUM_OFFSET;
parameter CV_VP_CYCLE_COUNTER_BASE     = CV_VP_REGISTER_BASE + CV_VP_CYCLE_COUNTER_OFFSET;
parameter CV_VP_STATUS_FLAGS_BASE      = CV_VP_REGISTER_BASE + CV_VP_STATUS_FLAGS_OFFSET;
parameter CV_VP_INTR_TIMER_BASE        = CV_VP_REGISTER_BASE + CV_VP_INTR_TIMER_OFFSET;
parameter CV_VP_DEBUG_CONTROL_BASE     = CV_VP_REGISTER_BASE + CV_VP_DEBUG_CONTROL_OFFSET;
parameter CV_VP_OBI_SLV_RESP_BASE      = CV_VP_REGISTER_BASE + CV_VP_OBI_SLV_RESP_OFFSET;
parameter CV_VP_SIG_WRITER_BASE        = CV_VP_REGISTER_BASE + CV_VP_SIG_WRITER_OFFSET;
parameter CV_VP_FENCEI_TAMPER_BASE     = CV_VP_REGISTER_BASE + CV_VP_FENCEI_TAMPER_OFFSET;

//XPULP instructions custom opcodes
parameter OPCODE_CUSTOM_0 = 7'h0b;
parameter OPCODE_CUSTOM_1 = 7'h2b;
parameter OPCODE_CUSTOM_2 = 7'h5b;
parameter OPCODE_CUSTOM_3 = 7'h7b;

//Xpulp instr coverpoints for each xpulp instr encoding is derived from
//xpulp encodings defined in User-Manual-en-cv32e40p_xxxxxx.pdf

// XPULP CUSTOM_0 ENCODING
parameter INSTR_CV_LB_PI_RI         =    {17'b?, 3'b000, 5'b?, OPCODE_CUSTOM_0};
parameter INSTR_CV_LH_PI_RI         =    {17'b?, 3'b001, 5'b?, OPCODE_CUSTOM_0};
parameter INSTR_CV_LW_PI_RI         =    {17'b?, 3'b010, 5'b?, OPCODE_CUSTOM_0};
parameter INSTR_CV_ELW_PI_RI        =    {17'b?, 3'b011, 5'b?, OPCODE_CUSTOM_0};
parameter INSTR_CV_LBU_PI_RI        =    {17'b?, 3'b100, 5'b?, OPCODE_CUSTOM_0};
parameter INSTR_CV_LHU_PI_RI        =    {17'b?, 3'b101, 5'b?, OPCODE_CUSTOM_0};
parameter INSTR_CV_BEQIMM           =    {17'b?, 3'b110, 5'b?, OPCODE_CUSTOM_0};
parameter INSTR_CV_BNEIMM           =    {17'b?, 3'b111, 5'b?, OPCODE_CUSTOM_0};

// XPULP CUSTOM_1 ENCODING
parameter INSTR_CV_LB_PI_RR         =    {7'b0000000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_LH_PI_RR         =    {7'b0000001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_LW_PI_RR         =    {7'b0000010, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_LBU_PI_RR        =    {7'b0001000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_LHU_PI_RR        =    {7'b0001001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

parameter INSTR_CV_LB_RR            =    {7'b0000100, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_LH_RR            =    {7'b0000101, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_LW_RR            =    {7'b0000110, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_LBU_RR           =    {7'b0001100, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_LHU_RR           =    {7'b0001101, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

parameter INSTR_CV_SB_PI_RI         =    {7'b???????, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_SH_PI_RI         =    {7'b???????, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_SW_PI_RI         =    {7'b???????, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_1};

parameter INSTR_CV_SB_PI_RR         =    {7'b0010000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_SH_PI_RR         =    {7'b0010001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_SW_PI_RR         =    {7'b0010010, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

parameter INSTR_CV_SB_RR            =    {7'b0010100, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_SH_RR            =    {7'b0010101, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_SW_RR            =    {7'b0010110, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

parameter INSTR_CV_STARTI           =    {12'b?, 5'b00000, 3'b100, 4'b0000, 1'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_START            =    {12'b0, 5'b?????, 3'b100, 4'b0001, 1'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_ENDI             =    {12'b?, 5'b00000, 3'b100, 4'b0010, 1'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_END              =    {12'b0, 5'b?????, 3'b100, 4'b0011, 1'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_COUNTI           =    {12'b?, 5'b00000, 3'b100, 4'b0100, 1'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_COUNT            =    {12'b0, 5'b?????, 3'b100, 4'b0101, 1'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_SETUPI           =    {12'b?, 5'b?????, 3'b100, 4'b0110, 1'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_SETUP            =    {12'b?, 5'b?????, 3'b100, 4'b0111, 1'b?, OPCODE_CUSTOM_1};

parameter INSTR_CV_EXTRACTR         =    {7'b0011000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_EXTRACTUR        =    {7'b0011001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_INSERTR          =    {7'b0011010, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_BCLRR            =    {7'b0011100, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_BSETR            =    {7'b0011101, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_ROR              =    {7'b0100000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_FF1              =    {7'b0100001, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_FL1              =    {7'b0100010, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_CLB              =    {7'b0100011, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_CNT              =    {7'b0100100, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

parameter INSTR_CV_ABS              =    {7'b0101000, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_SLET             =    {7'b0101001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_SLETU            =    {7'b0101010, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_MIN              =    {7'b0101011, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_MINU             =    {7'b0101100, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_MAX              =    {7'b0101101, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_MAXU             =    {7'b0101110, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_EXTHS            =    {7'b0110000, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_EXTHZ            =    {7'b0110001, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_EXTBS            =    {7'b0110010, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_EXTBZ            =    {7'b0110011, 5'b0, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_CLIP             =    {7'b0111000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_CLIPU            =    {7'b0111001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_CLIPR            =    {7'b0111010, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_CLIPUR           =    {7'b0111011, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

parameter INSTR_CV_ADDNR            =    {7'b1000000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_ADDUNR           =    {7'b1000001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_ADDRNR           =    {7'b1000010, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_ADDURNR          =    {7'b1000011, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_SUBNR            =    {7'b1000100, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_SUBUNR           =    {7'b1000101, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_SUBRNR           =    {7'b1000110, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_SUBURNR          =    {7'b1000111, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

parameter INSTR_CV_MAC              =    {7'b1001000, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};
parameter INSTR_CV_MSU              =    {7'b1001001, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_1};

// XPULP CUSTOM_2 ENCODING
parameter INSTR_CV_EXTRACT          =    {2'b00, 5'b?, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_EXTRACTU         =    {2'b01, 5'b?, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_INSERT           =    {2'b10, 5'b?, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_BCLR             =    {2'b00, 5'b?, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_BSET             =    {2'b01, 5'b?, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_BITREV           =    {2'b11, 5'b?, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_2};

parameter INSTR_CV_ADDN             =    {2'b00, 5'b?, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_ADDUN            =    {2'b01, 5'b?, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_ADDRN            =    {2'b10, 5'b?, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_ADDURN           =    {2'b11, 5'b?, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_SUBN             =    {2'b00, 5'b?, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_SUBUN            =    {2'b01, 5'b?, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_SUBRN            =    {2'b10, 5'b?, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_SUBURN           =    {2'b11, 5'b?, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_2};

parameter INSTR_CV_MULSN            =    {2'b00, 5'b?, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_MULHHSN          =    {2'b01, 5'b?, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_MULSRN           =    {2'b10, 5'b?, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_MULHHSRN         =    {2'b11, 5'b?, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_MULUN            =    {2'b00, 5'b?, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_MULHHUN          =    {2'b01, 5'b?, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_MULURN           =    {2'b10, 5'b?, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_MULHHURN         =    {2'b11, 5'b?, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_MACSN            =    {2'b00, 5'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_MACHHSN          =    {2'b01, 5'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_MACSRN           =    {2'b10, 5'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_MACHHSRN         =    {2'b11, 5'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_MACUN            =    {2'b00, 5'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_MACHHUN          =    {2'b01, 5'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_MACURN           =    {2'b10, 5'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_2};
parameter INSTR_CV_MACHHURN         =    {2'b11, 5'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_2};

// XPULP CUSTOM_3 ENCODING
parameter INSTR_CV_ADD_H            =    {5'b00000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_ADD_SC_H         =    {5'b00000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_ADD_SCI_H        =    {5'b00000, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_ADD_B            =    {5'b00000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_ADD_SC_B         =    {5'b00000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_ADD_SCI_B        =    {5'b00000, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_SUB_H            =    {5'b00001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SUB_SC_H         =    {5'b00001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SUB_SCI_H        =    {5'b00001, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SUB_B            =    {5'b00001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SUB_SC_B         =    {5'b00001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SUB_SCI_B        =    {5'b00001, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_AVG_H            =    {5'b00010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_AVG_SC_H         =    {5'b00010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_AVG_SCI_H        =    {5'b00010, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_AVG_B            =    {5'b00010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_AVG_SC_B         =    {5'b00010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_AVG_SCI_B        =    {5'b00010, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_AVGU_H           =    {5'b00011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_AVGU_SC_H        =    {5'b00011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_AVGU_SCI_H       =    {5'b00011, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_AVGU_B           =    {5'b00011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_AVGU_SC_B        =    {5'b00011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_AVGU_SCI_B       =    {5'b00011, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_MIN_H            =    {5'b00100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MIN_SC_H         =    {5'b00100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MIN_SCI_H        =    {5'b00100, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MIN_B            =    {5'b00100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MIN_SC_B         =    {5'b00100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MIN_SCI_B        =    {5'b00100, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_MINU_H           =    {5'b00101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MINU_SC_H        =    {5'b00101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MINU_SCI_H       =    {5'b00101, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MINU_B           =    {5'b00101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MINU_SC_B        =    {5'b00101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MINU_SCI_B       =    {5'b00101, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_MAX_H            =    {5'b00110, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MAX_SC_H         =    {5'b00110, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MAX_SCI_H        =    {5'b00110, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MAX_B            =    {5'b00110, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MAX_SC_B         =    {5'b00110, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MAX_SCI_B        =    {5'b00110, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_MAXU_H           =    {5'b00111, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MAXU_SC_H        =    {5'b00111, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MAXU_SCI_H       =    {5'b00111, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MAXU_B           =    {5'b00111, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MAXU_SC_B        =    {5'b00111, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_MAXU_SCI_B       =    {5'b00111, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_SRL_H            =    {5'b01000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SRL_SC_H         =    {5'b01000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SRL_SCI_H        =    {5'b01000, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SRL_B            =    {5'b01000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SRL_SC_B         =    {5'b01000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SRL_SCI_B        =    {5'b01000, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_SRA_H            =    {5'b01001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SRA_SC_H         =    {5'b01001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SRA_SCI_H        =    {5'b01001, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SRA_B            =    {5'b01001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SRA_SC_B         =    {5'b01001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SRA_SCI_B        =    {5'b01001, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_SLL_H            =    {5'b01010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SLL_SC_H         =    {5'b01010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SLL_SCI_H        =    {5'b01010, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SLL_B            =    {5'b01010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SLL_SC_B         =    {5'b01010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SLL_SCI_B        =    {5'b01010, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_OR_H             =    {5'b01011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_OR_SC_H          =    {5'b01011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_OR_SCI_H         =    {5'b01011, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_OR_B             =    {5'b01011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_OR_SC_B          =    {5'b01011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_OR_SCI_B         =    {5'b01011, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_XOR_H            =    {5'b01100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_XOR_SC_H         =    {5'b01100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_XOR_SCI_H        =    {5'b01100, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_XOR_B            =    {5'b01100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_XOR_SC_B         =    {5'b01100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_XOR_SCI_B        =    {5'b01100, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_AND_H            =    {5'b01101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_AND_SC_H         =    {5'b01101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_AND_SCI_H        =    {5'b01101, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_AND_B            =    {5'b01101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_AND_SC_B         =    {5'b01101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_AND_SCI_B        =    {5'b01101, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_ABS_H            =    {5'b01110, 1'b0, 1'b0, 5'b0, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_ABS_B            =    {5'b01110, 1'b0, 1'b0, 5'b0, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_DOTUP_H          =    {5'b10000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_DOTUP_SC_H       =    {5'b10000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_DOTUP_SCI_H      =    {5'b10000, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_DOTUP_B          =    {5'b10000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_DOTUP_SC_B       =    {5'b10000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_DOTUP_SCI_B      =    {5'b10000, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_DOTUSP_H         =    {5'b10001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_DOTUSP_SC_H      =    {5'b10001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_DOTUSP_SCI_H     =    {5'b10001, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_DOTUSP_B         =    {5'b10001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_DOTUSP_SC_B      =    {5'b10001, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_DOTUSP_SCI_B     =    {5'b10001, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_DOTSP_H          =    {5'b10010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_DOTSP_SC_H       =    {5'b10010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_DOTSP_SCI_H      =    {5'b10010, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_DOTSP_B          =    {5'b10010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_DOTSP_SC_B       =    {5'b10010, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_DOTSP_SCI_B      =    {5'b10010, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_SDOTUP_H         =    {5'b10011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SDOTUP_SC_H      =    {5'b10011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SDOTUP_SCI_H     =    {5'b10011, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SDOTUP_B         =    {5'b10011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SDOTUP_SC_B      =    {5'b10011, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SDOTUP_SCI_B     =    {5'b10011, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_SDOTUSP_H        =    {5'b10100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SDOTUSP_SC_H     =    {5'b10100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SDOTUSP_SCI_H    =    {5'b10100, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SDOTUSP_B        =    {5'b10100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SDOTUSP_SC_B     =    {5'b10100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SDOTUSP_SCI_B    =    {5'b10100, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_SDOTSP_H         =    {5'b10101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SDOTSP_SC_H      =    {5'b10101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SDOTSP_SCI_H     =    {5'b10101, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SDOTSP_B         =    {5'b10101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SDOTSP_SC_B      =    {5'b10101, 1'b0, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SDOTSP_SCI_B     =    {5'b10101, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_EXTRACT_H        =    {5'b10111, 1'b0, 1'b?, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_EXTRACT_B        =    {5'b10111, 1'b0, 1'b?, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_EXTRACTU_H       =    {5'b10111, 1'b0, 1'b?, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_EXTRACTU_B       =    {5'b10111, 1'b0, 1'b?, 5'b?, 5'b?, 3'b011, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_INSERT_H         =    {5'b10111, 1'b0, 1'b?, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_INSERT_B         =    {5'b10111, 1'b0, 1'b?, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_SHUFFLE_H        =    {5'b11000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SHUFFLE_SCI_H    =    {5'b11000, 1'b0, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SHUFFLE_B        =    {5'b11000, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SHUFFLEI0_SCI_B  =    {5'b11000, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SHUFFLEI1_SCI_B  =    {5'b11001, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SHUFFLEI2_SCI_B  =    {5'b11010, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SHUFFLEI3_SCI_B  =    {5'b11011, 1'b0, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SHUFFLE2_H       =    {5'b11100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SHUFFLE2_B       =    {5'b11100, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_PACK             =    {5'b11110, 1'b0, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_PACK_H           =    {5'b11110, 1'b0, 1'b1, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_PACKHI_B         =    {5'b11111, 1'b0, 1'b1, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_PACKLO_B         =    {5'b11111, 1'b0, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_CMPEQ_H          =    {5'b00000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPEQ_SC_H       =    {5'b00000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPEQ_SCI_H      =    {5'b00000, 1'b1, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPEQ_B          =    {5'b00000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPEQ_SC_B       =    {5'b00000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPEQ_SCI_B      =    {5'b00000, 1'b1, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_CMPNE_H          =    {5'b00001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPNE_SC_H       =    {5'b00001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPNE_SCI_H      =    {5'b00001, 1'b1, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPNE_B          =    {5'b00001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPNE_SC_B       =    {5'b00001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPNE_SCI_B      =    {5'b00001, 1'b1, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_CMPGT_H          =    {5'b00010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGT_SC_H       =    {5'b00010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGT_SCI_H      =    {5'b00010, 1'b1, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGT_B          =    {5'b00010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGT_SC_B       =    {5'b00010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGT_SCI_B      =    {5'b00010, 1'b1, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_CMPGE_H          =    {5'b00011, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGE_SC_H       =    {5'b00011, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGE_SCI_H      =    {5'b00011, 1'b1, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGE_B          =    {5'b00011, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGE_SC_B       =    {5'b00011, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGE_SCI_B      =    {5'b00011, 1'b1, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_CMPLT_H          =    {5'b00100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLT_SC_H       =    {5'b00100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLT_SCI_H      =    {5'b00100, 1'b1, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLT_B          =    {5'b00100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLT_SC_B       =    {5'b00100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLT_SCI_B      =    {5'b00100, 1'b1, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_CMPLE_H          =    {5'b00101, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLE_SC_H       =    {5'b00101, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLE_SCI_H      =    {5'b00101, 1'b1, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLE_B          =    {5'b00101, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLE_SC_B       =    {5'b00101, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLE_SCI_B      =    {5'b00101, 1'b1, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_CMPGTU_H         =    {5'b00110, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGTU_SC_H      =    {5'b00110, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGTU_SCI_H     =    {5'b00110, 1'b1, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGTU_B         =    {5'b00110, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGTU_SC_B      =    {5'b00110, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGTU_SCI_B     =    {5'b00110, 1'b1, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_CMPGEU_H         =    {5'b00111, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGEU_SC_H      =    {5'b00111, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGEU_SCI_H     =    {5'b00111, 1'b1, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGEU_B         =    {5'b00111, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGEU_SC_B      =    {5'b00111, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPGEU_SCI_B     =    {5'b00111, 1'b1, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_CMPLTU_H         =    {5'b01000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLTU_SC_H      =    {5'b01000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLTU_SCI_H     =    {5'b01000, 1'b1, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLTU_B         =    {5'b01000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLTU_SC_B      =    {5'b01000, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLTU_SCI_B     =    {5'b01000, 1'b1, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_CMPLEU_H         =    {5'b01001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLEU_SC_H      =    {5'b01001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLEU_SCI_H     =    {5'b01001, 1'b1, 1'b?, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLEU_B         =    {5'b01001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b001, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLEU_SC_B      =    {5'b01001, 1'b1, 1'b0, 5'b?, 5'b?, 3'b101, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CMPLEU_SCI_B     =    {5'b01001, 1'b1, 1'b?, 5'b?, 5'b?, 3'b111, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_CPLXMUL_R        =    {5'b01010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CPLXMUL_R_DIV2   =    {5'b01010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CPLXMUL_R_DIV4   =    {5'b01010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CPLXMUL_R_DIV8   =    {5'b01010, 1'b1, 1'b0, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_CPLXMUL_I        =    {5'b01010, 1'b1, 1'b1, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CPLXMUL_I_DIV2   =    {5'b01010, 1'b1, 1'b1, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CPLXMUL_I_DIV4   =    {5'b01010, 1'b1, 1'b1, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_CPLXMUL_I_DIV8   =    {5'b01010, 1'b1, 1'b1, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_CPLXCONJ         =    {5'b01011, 1'b1, 1'b0, 5'b0, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_SUBROTMJ         =    {5'b01100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b000, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SUBROTMJ_DIV2    =    {5'b01100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SUBROTMJ_DIV4    =    {5'b01100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SUBROTMJ_DIV8    =    {5'b01100, 1'b1, 1'b0, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_ADD_DIV2         =    {5'b01101, 1'b1, 1'b0, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_ADD_DIV4         =    {5'b01101, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_ADD_DIV8         =    {5'b01101, 1'b1, 1'b0, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};

parameter INSTR_CV_SUB_DIV2         =    {5'b01110, 1'b1, 1'b0, 5'b?, 5'b?, 3'b010, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SUB_DIV4         =    {5'b01110, 1'b1, 1'b0, 5'b?, 5'b?, 3'b100, 5'b?, OPCODE_CUSTOM_3};
parameter INSTR_CV_SUB_DIV8         =    {5'b01110, 1'b1, 1'b0, 5'b?, 5'b?, 3'b110, 5'b?, OPCODE_CUSTOM_3};

parameter APU_OP_FMADD              =    {6'h00};
parameter APU_OP_FNMSUB             =    {6'h01};
parameter APU_OP_FADD               =    {6'h02};
parameter APU_OP_FMUL               =    {6'h03};
parameter APU_OP_FDIV               =    {6'h04};
parameter APU_OP_FSQRT              =    {6'h05};
parameter APU_OP_FSGNJ              =    {6'h06};
parameter APU_OP_FMINMAX            =    {6'h07};
parameter APU_OP_FCMP               =    {6'h08};
parameter APU_OP_FCLASSIFY          =    {6'h09};
parameter APU_OP_F2F                =    {6'h0A};
parameter APU_OP_F2I                =    {6'h0B};
parameter APU_OP_I2F                =    {6'h0C};

parameter APU_OP_FMSUB              =    {6'h10};
parameter APU_OP_FNMADD             =    {6'h11};
parameter APU_OP_FSUB               =    {6'h12};
parameter APU_OP_FSGNJ_SE           =    {6'h16};
parameter APU_OP_F2I_U              =    {6'h1B};
parameter APU_OP_I2F_U              =    {6'h1C};

`ifdef FPU_ADDMUL_LAT
    `define FPU_LAT_``FPU_ADDMUL_LAT``_CYC
`else
    `define FPU_LAT_0_CYC
`endif

`endif // __UVME_CV32E40P_CONSTANTS_SV__
