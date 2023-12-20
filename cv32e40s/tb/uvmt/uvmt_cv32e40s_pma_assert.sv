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


// Description:
//   Module with assertions for the PMA.
//   Note, for historical reasons, some verification-written PMA assertions are
//   located among the design assertions in the core's repo. New asserts that
//   have been written after that fact, are here in this module.


`default_nettype none


module  uvmt_cv32e40s_pma_assert
  import cv32e40s_pkg::*;
  import uvm_pkg::*;
  import uvmt_cv32e40s_base_test_pkg::*;
#(
  parameter type          CORE_REQ_TYPE,
  parameter logic [31:0]  DM_REGION_START,
  parameter logic [31:0]  DM_REGION_END,
  parameter logic         IS_INSTR_SIDE,
  parameter int           PMA_NUM_REGIONS,
  parameter pma_cfg_t     PMA_CFG [PMA_NUM_REGIONS-1:0]
)(
  input wire  clk,
  input wire  rst_n,

  // Interface from Core
  input CORE_REQ_TYPE  core_trans_i,

  // Interface towards OBI
  input CORE_REQ_TYPE  bus_trans_o,
  input wire           bus_trans_ready_i,
  input wire           bus_trans_valid_o,

  // Writebuffer Signals
  input wire obi_data_req_t  writebuf_trans_i,
  input wire obi_data_req_t  writebuf_trans_o,
  input wire                 writebuf_ready_o,

  // PMA Verdict
  input wire  pma_err,
  input wire  bus_trans_bufferable,
  input wire  bus_trans_cacheable,
  input wire  bus_trans_integrity,

  // Support Logic
  uvma_obi_memory_if_t     obi_memory_if,
  uvma_rvfi_instr_if_t     rvfi_instr_if,
  input wire pma_status_t  pma_status_i
);


  default clocking @(posedge clk); endclocking
  default disable iff !rst_n;

  string info_tag = "CV32E40S_PMA_ASSERT";

  enum {BIT_IDX_BUFFERABLE=0} memtype_bit_idx_e;


  // Helper logic

  function logic  is_bufferable_in_config;
    is_bufferable_in_config = 0;
    foreach (PMA_CFG[i]) begin
      if (PMA_CFG[i].bufferable) begin
        is_bufferable_in_config = 1;
        //TODO:WARNING:silabs-robin Incorrect if region is overshadowed
      end
    end
  endfunction : is_bufferable_in_config
  localparam logic  IS_BUFFERABLE_IN_CONFIG = is_bufferable_in_config();


  // PMA-restricted regions prohibit OBI req  (vplan:InstructionFetches:2)

  a_req_prohibited: assert property (
    pma_err
    |->
    !bus_trans_valid_o
    //TODO:INFO:silas-robin Idea: rvfi-vs-obi sb refmodel prediction
  ) else `uvm_error(info_tag, "pma must block obi reqs");


  // memtype[0] matches bufferable flag  (vplan:InstructionFetches:0, vplan:DataFetches:0)

  a_memtype_bufferable: assert property (
    bus_trans_o.memtype[BIT_IDX_BUFFERABLE] == bus_trans_bufferable
    // Note: Depends on rest of checking to see that "bus_trans_bufferable" is reliable
  ) else `uvm_error(info_tag, "MPU bufferable flag must corespond to obi memtype[0]");


  // DM region overrules PMA configs  (vplan:DebugRange)

  a_dm_region: assert property (
    core_trans_i.dbg  &&
    (core_trans_i.addr inside {[DM_REGION_START:DM_REGION_END]})
    |->
    !pma_err
  ) else `uvm_error(info_tag, "dmode in dregion is never blocked");


  // Writebuffer usage must be bufferable  (vplan:WriteBuffer)

  if (!IS_INSTR_SIDE) begin: gen_writebuf
    a_writebuf_bufferable: assert property (
      !bus_trans_bufferable
      |->
      (writebuf_trans_i == writebuf_trans_o)  // Non-buffable must passthrough...
      ||
      (!writebuf_ready_o)    // ...or we are waiting for a previous buffered.
    ) else `uvm_error(info_tag, "Non-bufferable regions must pass straight through the writebuf");

    if (IS_BUFFERABLE_IN_CONFIG) begin: gen_buffering
      cov_writebuf_buffering: cover property (
        (writebuf_trans_i != writebuf_trans_o)
      );
    end : gen_buffering

    if (PMA_NUM_REGIONS == 0) begin: gen_noregions_nobuf
      a_writebuf_noregions: assert property (
        !bus_trans_bufferable  &&
        (writebuf_trans_i == writebuf_trans_o)
      ) else `uvm_error(info_tag, "with zero regions, nothing is bufferable");
    end : gen_noregions_nobuf
  end : gen_writebuf


  // After PMA-deny, subsequent accesses are also suppressed  (vplan:"Multi-memory operation instructions")

  a_failure_denies_subsequents_loads: assert property (
    rvfi_instr_if.is_pma_data_fault
    |->
    (rvfi_instr_if.rvfi_mem_rmask != rvfi_instr_if.rvfi_mem_rmask_intended)
    ||
    (rvfi_instr_if.rvfi_mem_rmask == 'd 0)
  ) else `uvm_error(info_tag, "accesses aftmr pma fault should be suppressed");

  a_failure_denies_subsequents_stores: assert property (
    rvfi_instr_if.is_pma_data_fault
    |->
    (rvfi_instr_if.rvfi_mem_wmask != rvfi_instr_if.rvfi_mem_wmask_intended)
    ||
    (rvfi_instr_if.rvfi_mem_wmask == 'd 0)
  ) else `uvm_error(info_tag, "accesses aftmr pma fault should be suppressed");

  property p_partial_pma_allow (exc_cause);
    rvfi_instr_if.rvfi_valid  &&
    (rvfi_instr_if.rvfi_mem_wmask || rvfi_instr_if.rvfi_mem_rmask)  &&
    rvfi_instr_if.rvfi_trap  &&
    rvfi_instr_if.rvfi_trap.exception  &&
    (rvfi_instr_if.rvfi_trap.cause_type == 0)  &&  // PMA, not PMP
    (rvfi_instr_if.rvfi_trap.exception_cause == exc_cause)
    //TODO:WARNING:silabs-robin Review after above rvfi bug is fixed
    ;
  endproperty : p_partial_pma_allow

  cov_partial_pma_allow_load: cover property (
    p_partial_pma_allow (EXC_CAUSE_LOAD_FAULT)
  );

  cov_partial_pma_allow_store: cover property (
    p_partial_pma_allow (EXC_CAUSE_STORE_FAULT)
  );


  // PMA-deny on instr, no mem op  (vplan: Not a vplan item. Inspo from a_failure_denies_subsequents.)

  a_failure_denies_memops: assert property (
    rvfi_instr_if.is_pma_instr_fault
    |->
    (rvfi_instr_if.rvfi_mem_wmask == '0)  &&
    (rvfi_instr_if.rvfi_mem_rmask == '0)
  ) else `uvm_error(info_tag, "pma-blocked instrs shouldn't access the bus");


  // MPU-accepted transactions must reach OBI  (vplan: not a vplan item)

  property p_eventually_mpu2obi;
    logic [31:0]  addr;
    (bus_trans_valid_o && bus_trans_ready_i, addr = bus_trans_o.addr)
    |->
    s_eventually (obi_memory_if.req && (obi_memory_if.addr[31:2] == addr[31:2]))
    //TODO:INFO:silabs-robin Could use transaction number ID instead of addr
    ;
  endproperty : p_eventually_mpu2obi

  a_eventually_mpu2obi: assert property (
    p_eventually_mpu2obi
  ) else `uvm_error(info_tag, "mpu output must reach the bus");


  // MPU output reliably reaches OBI  (vplan: not a vplan item)

  if (IS_INSTR_SIDE) begin: gen_attr_instr
    a_attributes_to_obi: assert property (
      bus_trans_valid_o  &&
      bus_trans_ready_i
      |->
      (obi_memory_if.memtype   == bus_trans_o.memtype)  &&
      (obi_memory_if.prot      == bus_trans_o.prot)     &&
      (obi_memory_if.dbg       == bus_trans_o.dbg)
    ) else `uvm_error(info_tag, "obi attributes must mach mpu");
    //TODO:INFO:silabs-robin Data-side Could be checked by comparing with transaction number IDs
  end : gen_attr_instr


  // PMA Verdict Expected

  a_pma_err: assert property (
    pma_err == !pma_status_i.allow
  ) else `uvm_error(info_tag, "pma err unexpected value");

  a_pma_bufferable: assert property (
    bus_trans_bufferable == pma_status_i.bufferable
  ) else `uvm_error(info_tag, "pma bufferable unexpected value");

  a_pma_cacheable: assert property (
    bus_trans_cacheable == pma_status_i.cacheable
  ) else `uvm_error(info_tag, "pma cacheable unexpected value");

  a_pma_integrity: assert property (
    bus_trans_integrity == pma_status_i.integrity
  ) else `uvm_error(info_tag, "pma integrity unexpected value");


endmodule : uvmt_cv32e40s_pma_assert


`default_nettype wire
