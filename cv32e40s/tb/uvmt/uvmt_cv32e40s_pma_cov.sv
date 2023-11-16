// Copyright 2023 Silicon Labs, Inc.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0.
//
// You may obtain a copy of the License at
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.


`default_nettype none


module  uvmt_cv32e40s_pma_cov
  import uvmt_cv32e40s_base_test_pkg::*;
#(
  parameter bit  IS_INSTR_SIDE,
  parameter int  PMA_NUM_REGIONS,
  parameter type CORE_REQ_TYPE
)(
  input wire  clk,
  input wire  clk_ungated,
  input wire  rst_n,

  // MPU Signals
  input CORE_REQ_TYPE  core_trans_i,
  input wire           core_trans_pushpop_i,
  input wire           core_trans_ready_o,
  input wire           core_trans_valid_i,
  input wire           load_access,
  input wire           misaligned_access_i,

  // Helper Logic
  input wire pma_status_t  pma_status_i,
  input wire pma_status_t  pma_status_rvfidata_word0highbyte_i,
  input wire pma_status_t  pma_status_rvfidata_word0lowbyte_i,
  uvma_rvfi_instr_if_t     rvfi_if
);


  // Exclude Known Unreachables

  `ifdef FORMAL
    localparam bit  SIMPLIFY_FV = 1;
  `else
    localparam bit  SIMPLIFY_FV = 0;
  `endif


  // Helper Logic - Match Info

  wire logic [31:0]  num_matches;
  assign  num_matches = $countones(pma_status_i.match_list);

  let  have_match = pma_status_i.have_match;
  let  match_idx  = pma_status_i.match_idx;


  // Helper Logic - MPU Activation

  wire logic  is_mpu_activated;
  assign  is_mpu_activated = (core_trans_ready_o && core_trans_valid_i);


  // Helper Logic - Split Transactions Main vs I/O

  wire logic [1:0]  rvfi_pmamain_lowhigh;
  assign  rvfi_pmamain_lowhigh[1] = pma_status_rvfidata_word0lowbyte_i.main;
  assign  rvfi_pmamain_lowhigh[0] = pma_status_rvfidata_word0highbyte_i.main;


  // typedef to parameterize size of helper signals
  typedef logic [$bits(rvfi_if.rvfi_mem_wmask)-1:0] rvfi_mem_wmask_t;

  // Helper Logic - "Past" Values
  var logic             occured_rvfi_valid;
  var logic             rvfi_pma_fault_q;
  var logic             rvfi_mem_act_q;
  var logic             rvfi_pmamain_low_q;
  var rvfi_mem_wmask_t  rvfi_mem_wmask_q;

  always_ff @(posedge clk_ungated or negedge rst_n) begin
    if (rst_n == 0) begin
      occured_rvfi_valid <= '0;
      rvfi_pma_fault_q   <= '0;
      rvfi_mem_wmask_q   <= '0;
      rvfi_mem_act_q     <= '0;
      rvfi_pmamain_low_q <= '0;
    end else if (rvfi_if.rvfi_valid) begin
      occured_rvfi_valid <= 1;
      rvfi_pma_fault_q   <= rvfi_if.is_pma_fault;
      rvfi_mem_wmask_q   <= rvfi_mem_wmask_t'(rvfi_if.rvfi_mem_wmask);
      rvfi_mem_act_q     <= rvfi_if.is_mem_act;
      rvfi_pmamain_low_q <= rvfi_pmamain_lowhigh[1];
    end
  end


  // MPU Coverage Definition

  covergroup cg_mpu @(posedge clk);
    option.per_instance = 1;
    option.detect_overlap = 1;

    // vplan:"Valid number of regions"
    cp_numregions: coverpoint  PMA_NUM_REGIONS {
      bins zero = {0}      with (PMA_NUM_REGIONS == 0);
      bins mid  = {[1:15]} with ((0 < PMA_NUM_REGIONS) && (PMA_NUM_REGIONS < 16));
      bins max  = {16}     with (PMA_NUM_REGIONS == 16);
    }

    // vplan:"Overlapping PMA Regions"
    cp_multimatch: coverpoint  num_matches  iff (is_mpu_activated) {
      bins zero = {0}
        with (!SIMPLIFY_FV);
      bins one  = {1}
        with (0 < PMA_NUM_REGIONS);
      bins many = {[2:PMA_NUM_REGIONS]}
        with ((1 < PMA_NUM_REGIONS) && (!SIMPLIFY_FV));
    }

    cp_matchregion: coverpoint  match_idx  iff (is_mpu_activated) {
      bins  regions[] = {[0:(PMA_NUM_REGIONS > 0) ? (PMA_NUM_REGIONS-1) : 0 ]}
        with (!SIMPLIFY_FV)
        iff (have_match == 1);
      bins  nomatch   = {[0:(PMA_NUM_REGIONS > 0) ? (PMA_NUM_REGIONS-1) : 0]}
        with (!SIMPLIFY_FV)
        iff (have_match == 0);
    }

    cp_aligned: coverpoint  misaligned_access_i  iff (is_mpu_activated) {
      bins          misaligned = {1} with (!IS_INSTR_SIDE);
      illegal_bins  illegal    = {1} with ( IS_INSTR_SIDE);
      bins          aligned    = {0};
    }

    cp_loadstoreexec: coverpoint  load_access  iff (is_mpu_activated) {
      bins  load  = {1}    with (!IS_INSTR_SIDE);
      bins  store = {0}    with (!IS_INSTR_SIDE);
      bins  exec  = {0, 1} with ( IS_INSTR_SIDE);
    }

    cp_store: coverpoint  load_access  iff (is_mpu_activated) {
      bins  store = {0}  with (!IS_INSTR_SIDE);
    }

    cp_allow: coverpoint  pma_status_i.allow  iff (is_mpu_activated) {
      bins allow    = {1};
      bins disallow = {0};
    }

    cp_main: coverpoint  pma_status_i.main  iff (is_mpu_activated) {
      bins main = {1};
      bins io   = {0};
    }

    cp_bufferable: coverpoint  pma_status_i.bufferable  iff (is_mpu_activated) {
      bins          bufferable    = {1} with (!IS_INSTR_SIDE);
      illegal_bins  illegal       = {1} with ( IS_INSTR_SIDE);
      bins          nonbufferable = {0};
    }

    cp_cacheable: coverpoint  pma_status_i.cacheable  iff (is_mpu_activated) {
      bins cacheable = {1};
      bins no        = {0};
    }

    cp_integrity: coverpoint  pma_status_i.integrity  iff (is_mpu_activated) {
      bins integrity = {1} with (!SIMPLIFY_FV);
      bins no        = {0};
    }

    cp_overridedm: coverpoint  pma_status_i.override_dm  iff (is_mpu_activated)
    {
      bins override = {1};
      bins no       = {0};
    }

    cp_pushpop: coverpoint  core_trans_pushpop_i  iff (is_mpu_activated) {
      bins          pushpop = {1} with (!IS_INSTR_SIDE);
      illegal_bins  illegal = {1} with ( IS_INSTR_SIDE);
      bins          no      = {0};
    }

    // vplan:DebugRange
    cp_dmregion: coverpoint  pma_status_i.accesses_dmregion
      iff (is_mpu_activated)
    {
      bins in  = {1};
      bins out = {0};
    }
    cp_dmode: coverpoint  core_trans_i.dbg  iff (is_mpu_activated) {
      bins dmode = {1};
      bins no    = {0};
    }

    cp_jvt: coverpoint  pma_status_i.accesses_jvt  iff (is_mpu_activated) {
      bins accesses = {1} with (IS_INSTR_SIDE);
      bins no       = {0} with (IS_INSTR_SIDE);
    }

    x_multimatch_aligned_loadstoreexec_allow:
      cross  cp_multimatch, cp_aligned, cp_loadstoreexec, cp_allow {
        ignore_bins  one_disallow =
          (binsof(cp_multimatch.one) && binsof(cp_allow.disallow))
          with (SIMPLIFY_FV);
      }
    x_multimatch_main: cross  cp_multimatch, cp_main {
      ignore_bins  one_io =
        (binsof(cp_multimatch.one) && binsof(cp_main.io)) with (SIMPLIFY_FV);
    }
    x_multimatch_bufferable: cross  cp_multimatch, cp_bufferable;
    x_multimatch_cacheable: cross  cp_multimatch, cp_cacheable {
      ignore_bins  one_no =
        (binsof(cp_multimatch.one) && binsof(cp_cacheable.no))
        with (SIMPLIFY_FV);
    }
    x_multimatch_integrity: cross  cp_multimatch, cp_integrity;
    x_multimatch_overridedm: cross  cp_multimatch, cp_overridedm {
      ignore_bins  one_override =
        (binsof(cp_multimatch.one) && binsof(cp_overridedm.override))
        with (SIMPLIFY_FV);
    }

    x_aligned_allow:              cross  cp_aligned, cp_allow;
    x_aligned_main_loadstoreexec: cross  cp_aligned, cp_main, cp_loadstoreexec;
    x_aligned_bufferable:         cross  cp_aligned, cp_bufferable;
    x_aligned_cacheable:          cross  cp_aligned, cp_cacheable;
    x_aligned_integrity:          cross  cp_aligned, cp_integrity;
    x_aligned_overridedm:         cross  cp_aligned, cp_overridedm;

    x_loadstoreexec_allow_main:   cross  cp_loadstoreexec, cp_allow, cp_main {
      ignore_bins  ignore =
        binsof(cp_allow.allow)  &&
        binsof(cp_main.io);
        //Note: Should be specific "illegal_bins"
        //Because of tool support, the covers are artificially limited.
      illegal_bins  disallow_main =
        binsof(cp_allow.disallow)  &&
        binsof(cp_main.main);
    }
    x_loadstoreexec_main_pushpop: cross  cp_loadstoreexec, cp_main, cp_pushpop;
    //x_loadstoreexec_bufferable:   cross  cp_loadstoreexec, cp_bufferable;
      //Note: Filtering of this cross seems impossible.
      //Each tool supports each their own disparate subset of the language, so
      //you can seemingly make it work in one or the other but not both at once.
      //See "x_store_bufferable"
    x_loadstoreexec_cacheable:    cross  cp_loadstoreexec, cp_cacheable;
    x_loadstoreexec_integrity:    cross  cp_loadstoreexec, cp_integrity;
    x_loadstoreexec_overridedm:   cross  cp_loadstoreexec, cp_overridedm;

    //TODO silabs-robin: Needs update
    //x_allow_bufferable: cross  cp_allow, cp_bufferable {
    //  ignore_bins  disallow_bufferable =
    //    (binsof(cp_allow.disallow) && binsof(cp_bufferable.bufferable))
    //    with (SIMPLIFY_FV);
    //}
    //x_allow_cacheable:  cross  cp_allow, cp_cacheable {
    //  illegal_bins  disallow_cacheable =
    //    binsof(cp_allow.disallow) && binsof(cp_cacheable.cacheable);
    //}
    //x_allow_integrity:  cross  cp_allow, cp_integrity {
    //  illegal_bins  disallow_integrity =
    //    binsof(cp_allow.disallow) && binsof(cp_integrity.integrity);
    //}
    x_allow_jvt:        cross  cp_allow, cp_jvt;

    x_dmregion_dmode: cross  cp_dmregion, cp_dmode;

    x_store_bufferable: cross  cp_store, cp_bufferable;

    //Note: more crosses are possible, but bordering on impractical/infeasible
  endgroup

  cg_mpu  mpu_cg = new;


  // RVFI Coverage Definition

  covergroup cg_rvfi @(posedge clk_ungated);
    option.per_instance = 1;
    option.detect_overlap = 1;

    cp_aligned: coverpoint  rvfi_if.is_split_datatrans_intended
      iff (rvfi_if.rvfi_valid)
    {
      bins  misaligned = {1};
      bins  aligned    = {0};
    }

    cp_pmafault: coverpoint  rvfi_if.is_pma_fault  iff (rvfi_if.rvfi_valid) {
      bins  fault = {1};
      bins  no    = {0};
    }

    cp_waspmafault: coverpoint  rvfi_pma_fault_q  iff (occured_rvfi_valid) {
      bins  fault = {1};
      bins  no    = {0};
    }

    cp_loadstore: coverpoint  rvfi_if.rvfi_mem_wmask
      iff (rvfi_if.is_mem_act)
    {
      bins  load  = {0};
      bins  store = {[1:$]};
      illegal_bins  undefined = default;  // Should be empty
    }

    cp_wasloadstore: coverpoint  rvfi_mem_wmask_q
      iff (rvfi_mem_act_q && occured_rvfi_valid)
    {
      bins  load  = {0};
      bins  store = {[1:$]};
      illegal_bins  undefined = default;  // Should be empty
    }

    cp_firstfail: coverpoint  pma_status_rvfidata_word0lowbyte_i.allow
      iff (rvfi_if.is_mem_act)
    {
      bins  yes = {0};
      bins  no  = {1};
    }

    cp_boundary: coverpoint  rvfi_pmamain_lowhigh  iff (rvfi_if.is_mem_act) {
      bins  main2main = {2'b 11};
      bins  main2io   = {2'b 10};
      bins  io2main   = {2'b 01};
      bins  io2io     = {2'b 00};
    }

    cp_wasmain: coverpoint  rvfi_pmamain_low_q
      iff (rvfi_mem_act_q && occured_rvfi_valid)
    {
      bins  main = {1};
      bins  io   = {0};
    }

    cp_tablejump: coverpoint  rvfi_if.is_tablejump_raw  iff (rvfi_if.rvfi_valid) {
      bins jump = {1};
      bins no   = {0};
    }

    cp_fence: coverpoint  rvfi_if.is_fencefencei  iff (rvfi_if.rvfi_valid) {
      bins fencefencei = {1};
      bins no          = {0};
    }


    // General Crosses

    x_aligned_pmafault_loadstore_firstfail:
      cross  cp_aligned, cp_pmafault, cp_loadstore, cp_firstfail;

    x_aligned_loadstore_boundary: cross  cp_aligned, cp_loadstore, cp_boundary {
      ignore_bins  aligned =
        binsof(cp_aligned.aligned);
      ignore_bins  misaligned_io2io =
        (binsof(cp_aligned.misaligned) && binsof(cp_boundary.io2io))
        with (SIMPLIFY_FV);
    }


    // Table Jump Crosses

    // TODO: silabs-hfegran: these need vector table access on IF side, currently
    // only data side is used.
    //x_pmafault_firstfail_tablejump: cross  cp_pmafault, cp_firstfail, cp_tablejump;

    x_pmafault_tablejump: cross  cp_pmafault, cp_tablejump;


    // Fence Crosses

    x_waspmafault_wasmain_wasloadstore_fence:
      cross  cp_waspmafault, cp_wasmain, cp_wasloadstore, cp_fence;
  endgroup

  if (!IS_INSTR_SIDE) begin: gen_rvfi_cg
    cg_rvfi  rvfi_cg = new;
    // RVFI is 1 interface, so we don't need an exact duplicate at each MPU.
  end


endmodule : uvmt_cv32e40s_pma_cov


`default_nettype wire
