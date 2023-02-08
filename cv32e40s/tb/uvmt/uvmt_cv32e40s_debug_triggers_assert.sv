//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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

module uvmt_cv32e40s_debug_trigger_assert
  import uvm_pkg::*;
  import uvma_rvfi_pkg::*;
  import cv32e40s_pkg::*;
  (
      uvma_rvfi_instr_if rvfi_if,
      //uvma_clknrst_if clknrst_if,
      logic clk,
      logic reset_n,
      //uvma_rvfi_csr_if csr_dcsr,
      //uvma_rvfi_csr_if csr_dpc,
      //uvma_rvfi_csr_if csr_mepc,
      //uvma_rvfi_csr_if csr_mstatus,
      //uvma_rvfi_csr_if csr_mtvec,
      uvma_rvfi_csr_if rvfi_tdata1_if,
      uvma_rvfi_csr_if rvfi_tdata2_if
      //uvmt_cv32e40s_debug_cov_assert_if debug_if
  );

/////////////////////////////////////////////////////////////////////////////////////////

  // Single clock, single reset design, use default clocking
  //default clocking @(posedge clknrst_if.clk); endclocking
  //default disable iff !(clknrst_if.reset_n);
  default clocking @(posedge clk); endclocking
  default disable iff !(reset_n);

    //tdata1:
    logic [31:0] tdata1;
    assign tdata1 = (rvfi_tdata1_if.rvfi_csr_rdata & rvfi_tdata1_if.rvfi_csr_rmask) | (rvfi_tdata1_if.rvfi_csr_wdata & rvfi_tdata1_if.rvfi_csr_wmask);

    logic tdata1_execute;
    assign tdata1_execute = tdata1[2];

    logic [3:0] tdata1_type;
    assign tdata1_type = tdata1[31:28];

    //tdata2:
    logic [31:0] tdata2;
    assign tdata2 = (rvfi_tdata2_if.rvfi_csr_rdata & rvfi_tdata2_if.rvfi_csr_rmask) | (rvfi_tdata2_if.rvfi_csr_wdata & rvfi_tdata2_if.rvfi_csr_wmask);


    a_dt_enter_dbg_instr_match: assert property(
        rvfi_if.rvfi_valid
        && (tdata1_type == 2 || tdata1_type == 6)
        && tdata1_execute
        && rvfi_if.rvfi_pc_rdata != 0
        && tdata2 == rvfi_if.rvfi_pc_rdata

        && rvfi_if.rvfi_dbg_mode
        //dbg_mode: viser om instruksjonen ble utført i debug mode eller normal mode.
        |->
        rvfi_if.rvfi_dbg
        //dbg: første instruksjonen i debug handleren som viser bl.a. hvorfor man går inn i debug mode
    );

    a_dt_enter_dbg_test: cover property(
        rvfi_if.rvfi_valid
        && rvfi_if.rvfi_dbg == 2
    );

/*
Må være oppfylt:
Enter debug mode by any of the above methods.
Write (randomized) breakpoint addr to tdata2 and enable breakpoint in tdata1[2]
Exit debug mode (dret instruction)
Select mcontrol6 for a trigger and enable instruction matching (relatert til at cause er 2?)
Write breakpoint addr to tdata2 register (when cause is 2?)
Verify:
-Verify that core enters debug mode on breakpoint addr
-Current PC is saved to DPC
-Cause of debug must be saved to DCSR (cause=2)
-PC is updated to value on dm_haltaddr_i input
-Core starts executing debug code
Gjenta:
For alle antall triggere.
Sjekk ut info:
Enter debug
tdata breakpoint/trigger address/cause (1,2,3)
Gå ut av debug
mcontrol og mcontrol6
Sjekk ut assertions:
A:  uvmt_cv32_tb.u_debug_assert.a_trigger_match
A:  uvmt_cv32_tb.u_debug_assert.a_debug_mode_pc
A:  uvmt_cv32_tb.u_debug_assert.a_enter_debug
Enter debug mode:
- haltreq eller resethaltreq er høy etter reset gjør at kjernen går direkte inn i debug mode
- ebreak intruksjonen på forskjellige måter
- cause:
  1) ebreak
  2) trigger
  3) haltreq
  4) step
  5) resethaltreq
  6) Group
Enable breakpoints, tdata1 or tdata2
- tdata1 er en felles betegnelse på CSRene mcontrol, mcontrol6, etrigger, disabled. Hvilken CSR tdata1 er er bestemt av type feltet i CSRene
- tdata2 er tilsvarende, men typen er bestemt av feltene type og dmode i tdata2.
dmode avgjør om registeret er tilgjengelig i debug eller machine mode.
CSRen lagrer adressen man skal trigge på  (altså load/store/execute), utenom dersom det er exception trigger. Da lagrer den andre spesifikke bit felt.
- tdata3 er ubrukt
Når debuggeren skriver 1 til clrresethaltq vil signalet halt_on_reset_req (?) klareres.
Signalet vil også cleares ved debug module reset
*/

endmodule : uvmt_cv32e40s_debug_trigger_assert
