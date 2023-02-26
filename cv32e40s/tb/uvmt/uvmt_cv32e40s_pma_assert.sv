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
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
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

  // Interface to OBI
  input CORE_REQ_TYPE  bus_trans_o,
  input wire           bus_trans_bufferable,
  input wire           bus_trans_ready_i,
  input wire           bus_trans_valid_o,

  // OBI Signals
  input wire         obi_req,
  input wire         obi_rvalid,
  input wire [31:0]  obi_addr,

  // Writebuffer Signals
  input obi_data_req_t  writebuf_trans_i,
  input obi_data_req_t  writebuf_trans_o,
  input wire            writebuf_ready_o,

  // PMA Verdict
  input wire  pma_err,

  // Support Interfaces
  uvmt_cv32e40s_support_logic_for_assert_coverage_modules_if.slave_mp  sup,
  uvma_rvfi_instr_if  rvfi
);


  default clocking @(posedge clk); endclocking
  default disable iff !rst_n;

  string info_tag = "CV32E40S_PMA_ASSERT";


  // Helper logic

  function logic  is_bufferable_in_config;
    is_bufferable_in_config = 0;
    foreach (PMA_CFG[i]) begin
      if (PMA_CFG[i].bufferable) begin
        is_bufferable_in_config = 1;
        //Note: Incorrect if region is overshadowed
      end
    end
  endfunction : is_bufferable_in_config
  localparam logic  IS_BUFFERABLE_IN_CONFIG = is_bufferable_in_config();


  // PMA-restricted regions prohibit OBI req  (vplan:InstructionFetches:2)

  a_req_prohibited: assert property (
    pma_err
    |->
    !bus_trans_valid_o
    //TODO:WARNING:silabs-robin Have not checked that "mpu -> obi"
    //TODO:WARNING:silabs-robin Have not checked that "rvfi -> mpu"
    //TODO:INFO:silas-robin Idea: rvfi-vs-obi sb refmodel prediction
  ) else `uvm_error(info_tag, "TODO");


  // memtype[0] matches bufferable flag  (vplan:InstructionFetches0, vplan:DataFetches:0)

  a_memtype_bufferable: assert property (
    bus_trans_o.memtype[0] == bus_trans_bufferable
    // Note: Depends on rest of checking to see that "bus_trans_bufferable is reliable
  ) else `uvm_error(info_tag, "TODO");


  // DM region overrules PMA configs  (vplan:DebugRange)

  a_dm_region: assert property (
    core_trans_i.dbg  &&
    (core_trans_i.addr inside {[DM_REGION_START:DM_REGION_END]})
    |->
    !pma_err
  ) else `uvm_error(info_tag, "TODO");


  // Writebuffer usage must be bufferable  (vplan:WriteBuffer)

  if (!IS_INSTR_SIDE) begin: gen_writebuf
    a_writebuf_bufferable: assert property (
      !bus_trans_bufferable
      |->
      (writebuf_trans_i == writebuf_trans_o)  // Non-buffable must passthrough...
      ||
      (!writebuf_ready_o)  // ...or we are waiting for a previous buffered.
    ) else `uvm_error(info_tag, "TODO");

    if (IS_BUFFERABLE_IN_CONFIG) begin: gen_buffering
      cov_writebuf_buffering: cover property (
        (writebuf_trans_i != writebuf_trans_o)
      );
    end : gen_buffering

    if (PMA_NUM_REGIONS == 0) begin: gen_noregions_nobuf
      a_writebuf_noregions: assert property (
        !bus_trans_bufferable  &&
        (writebuf_trans_i == writebuf_trans_o)
      ) else `uvm_error(info_tag, "TODO");
    end : gen_noregions_nobuf
  end : gen_writebuf


  // After PMA-deny, subsequent accesses are also suppressed

  a_TODO: assert property (
    rvfi.is_pma_fault
    |->
    (rvfi.rvfi_mem_wmask == '0)
    //TODO:ERROR:silabs-robin Zcmp should be able to break this
    //TODO:ERROR:silabs-robin Also reads
  ) else `uvm_error(info_tag, "TODO");

  cov_TODO: cover property (
    rvfi.rvfi_valid  &&
    rvfi.rvfi_trap   &&
    rvfi.rvfi_mem_wmask
  );


/*  TODO:ERROR:silabs-robin  Check mpu->obi, or delete this
  // TODO

  property p_TODO;
    logic [31:0]  addr;
    (bus_trans_valid_o && bus_trans_ready_i)  ##0
    (1, addr = bus_trans_o.addr)
    |->
    //(obi_req && (obi_addr == addr) [->1])
    s_eventually (obi_req && (obi_addr == addr))
    ;
  endproperty : p_TODO

  a_TODO: assert property (
    p_TODO
  ) else `uvm_error(info_tag, "TODO");


  // TODO

  asu_TODO: assume property (
    (sup.instr_bus_v_addr_ph_cnt > 0)
    |->
    s_eventually  obi_rvalid
  );
*/


endmodule : uvmt_cv32e40s_pma_assert


`default_nettype wire
