// Copyright 2023 Silicon Labs, Inc.
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

// -------------------------------------------------------------------
// This file holds typedefs related to the CSRs in the ISA decoder.
// -------------------------------------------------------------------

`ifndef __ISA_TYPEDEFS_CSR__
`define __ISA_TYPEDEFS_CSR__

  // -------------------------------------------------------------------
  // CSR Addresses
  // -------------------------------------------------------------------



  // TODO: expand
  typedef enum logic [31:20] {
    MSTATUS       = 12'h300,
    MISA          = 12'h301,
    MIE           = 12'h304,
    MTVEC         = 12'h305,
    MTVT          = 12'h307,
    MSTATUSH      = 12'h310,
    MCOUNTINHIBIT = 12'h320,
    MHPMEVENT3    = 12'h323,
    MHPMEVENT31   = 12'h33F,
    MSCRATCH      = 12'h340,
    MEPC          = 12'h341,
    MCAUSE        = 12'h342,
    MTVAL         = 12'h343,
    MIP           = 12'h344,
    MNXTI         = 12'h345,
    MINTSTATUS    = 12'h346,
    MINTTHRESH    = 12'h347,
    MSCRATCHCSW   = 12'h348,
    MSCRATCHCSWL  = 12'h349,
    MCLICBASE     = 12'h34A,
    MSECCFG       = 12'h747,
    TSELECT       = 12'h7A0,
    TDATA1        = 12'h7A1,
    TDATA2        = 12'h7A2,
    TDATA3        = 12'h7A3,
    TINFO         = 12'h7A4,
    TCONTROL      = 12'h7A5,
    DCSR          = 12'h7B0,
    DPC           = 12'h7B1,
    DSCRATCH0     = 12'h7B2,
    DSCRATCH1     = 12'h7B3,
    CPUCTRL       = 12'hBF0,
    SECURESEED0   = 12'hBF9,
    SECURESEED1   = 12'hBFA,
    SECURESEED2   = 12'hBFC
  } csr_name_e;

  // -------------------------------------------------------------------
  // CSR Types - TODO replace with include when autogen in place
  // -------------------------------------------------------------------
  typedef struct packed {
    logic [31:24] mil;
    logic [23:16] reserved;
    logic [15:8]  sil;
    logic [7:0]   uil;
  } mintstatus_t;

  typedef struct packed {
    logic [31:8] reserved_0;
    logic [7:0]  th;
  } mintthresh_t;

  typedef struct packed {
    logic [31:31] sd;
    logic [30:23] reserved_3;
    logic [22:22] tsr;
    logic [21:21] tw;
    logic [20:20] tvm;
    logic [19:19] mxr;
    logic [18:18] sum;
    logic [17:17] mprv;
    logic [16:15] xs;
    logic [14:13] fs;
    logic [12:11] mpp;
    logic [10:9]  vs;
    logic [8:8]   spp;
    logic [7:7]   mpie;
    logic [6:6]   ube;
    logic [5:5]   spie;
    logic [4:4]   reserved_2;
    logic [3:3]   mie;
    logic [2:2]   reserved_1;
    logic [1:1]   sie;
    logic [0:0]   reserved_0;
  } mstatus_t;

  // TODO non-clic union
  typedef struct packed {
    logic [31:7] base_31_7;
    logic [6:2]  base_6_2;
    logic [1:0]  mode;
  } mtvec_clic_t;

  // TODO CLIC_ID_WIDTH readable?
  localparam N_MTVT = 2+CLIC_ID_WIDTH > 6 ? 2+CLIC_ID_WIDTH : 6;

  typedef struct packed {
    logic [31:N_MTVT]  base_31_n;
    logic [N_MTVT-1:6] base_n_6;
    logic [5:0]        reserved;
  } mtvt_t;

  typedef struct packed {
    logic [31:1] m_exception_pc;
    logic [0:0]  reserved;
  } mepc_t;

  // TODO exccode_t core specific?
  typedef struct packed {
    logic [31:31] interrupt;
    logic [30:30] minhv;
    logic [29:28] mpp;
    logic [27:27] mpie;
    logic [26:24] reserved_1;
    logic [23:16] mpil;
    logic [15:12] reserved_0;
    logic [11:0]  exccode; // TODO typedef - core specific how to handle properly?
  } mcause_t;

  typedef struct packed {
    logic [31:28] debugver;
    logic [27:18] reserved_27_18;
    logic [17:17] ebreakvs;
    logic [16:16] ebreakvu;
    logic [15:15] ebreakm;
    logic [14:14] reserved_14;
    logic [13:13] ebreaks;
    logic [12:12] ebreaku;
    logic [11:11] stepie;
    logic [10:10] stopcount;
    logic [9:9]   stoptime;
    logic [8:6]   cause;
    logic [5:5]   v;
    logic [4:4]   mprven;
    logic [3:3]   nmip;
    logic [2:2]   step;
    logic [1:0]   prv;
  } dcsr_t;


`endif // __ISA_TYPEDEFS_CSR__
