// Copyright 2024 Torje Nygaard Eikenes
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

`ifndef __RVFI_COMPARE_SVA_SV__
`define __RVFI_COMPARE_SVA_SV__


/**
 * Compare the RVFI interface of the core and the reference model.
 * Use assertions to support potentially support formal verification
 */
module rvfi_compare_sva
  import uvma_rvfi_pkg::*;
  import uvm_pkg::*;
  (
    rvfi_if_t rvfi_core,
    rvfi_if_t rvfi_rm
  );

  string info_tag = "RVFI_COMPARE_ASSERT";

`define ASSERT_EQUAL(NAME) \
    a_``NAME: assert property( @(posedge rvfi_core.clk) \
      rvfi_rm.valid |-> (rvfi_rm.NAME == rvfi_core.NAME)) \
      else `uvm_error(info_tag, $sformatf("MISMATCH PC: %8h rvfi_rm.%s=%8h rvfi_core.%s=%8h", rvfi_rm.pc_rdata, `"NAME`" ,$sampled(rvfi_rm.NAME), `"NAME`", $sampled(rvfi_core.NAME)))

`define ASSERT_EQUAL_RANGE(NAME, FROM, TO) \
    a_``NAME: assert property( @(posedge rvfi_core.clk) \
      rvfi_rm.valid |-> (rvfi_rm.NAME``[FROM:TO] == rvfi_core.NAME``[FROM:TO])) \
      else `uvm_error(info_tag, $sformatf("MISMATCH PC: %8h rvfi_rm.%s=%8h rvfi_core.%s=%8h", rvfi_rm.pc_rdata, `"NAME`",$sampled(rvfi_rm.NAME), `"NAME`", $sampled(rvfi_core.NAME)))


  rvfi_valid_a: assert property( @(posedge rvfi_core.clk)
    rvfi_core.valid || rvfi_rm.valid |-> (rvfi_rm.valid == rvfi_core.valid))
    else `uvm_error(info_tag, $sformatf("MISMATCH PC: %8h rvfi_rm.valid=%0h rvfi_core.valid=%0h",$sampled(rvfi_core.pc_rdata),$sampled(rvfi_rm.valid), $sampled(rvfi_core.valid)));

  `ASSERT_EQUAL(pc_rdata)
  `ASSERT_EQUAL(insn)
  `ASSERT_EQUAL(trap)
  `ASSERT_EQUAL(halt)
  `ASSERT_EQUAL(dbg)
  `ASSERT_EQUAL(dbg_mode)
  `ASSERT_EQUAL(nmip)
  `ASSERT_EQUAL(intr)
  `ASSERT_EQUAL(mode)
  `ASSERT_EQUAL(rd1_addr)

  // TODO: Spike outputs wrong values for rs1_addr and rs2_addr
  //`ASSERT_EQUAL(rs1_addr)
  //`ASSERT_EQUAL(rs1_rdata)
  //`ASSERT_EQUAL(rs2_addr)
  //`ASSERT_EQUAL(rs2_rdata)

  // TODO: The following assertions cant use the macro because they require more conditions

  rvfi_rd1_wdata_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid && rvfi_rm.rd1_addr |-> (rvfi_rm.rd1_wdata == rvfi_core.rd1_wdata))
    else `uvm_error(info_tag, $sformatf("MISMATCH PC: %8h rvfi_rm.rd1_wdata=%0h rvfi_core.rd1_wdata=%0h",$sampled(rvfi_core.pc_rdata),$sampled(rvfi_rm.rd1_wdata), $sampled(rvfi_core.rd1_wdata)));

  // TODO: Add support for multiple memory writes to check all of mem_xmask, not only 4 bytes 
  `ASSERT_EQUAL_RANGE(mem_rmask, 3,0)
  `ASSERT_EQUAL_RANGE(mem_wmask, 3,0)

  rvfi_mem_addr_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and ((rvfi_core.mem_rmask || rvfi_core.mem_wmask))|-> (rvfi_rm.mem_addr[31:0] == rvfi_core.mem_addr[31:0]))
    else `uvm_error("RVFI_MEM_ADDR", $sformatf("MISMATCH PC: %0h rvfi_rm.mem_addr=%0h rvfi_core.mem_addr=%0h", $sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_addr), $sampled(rvfi_core.mem_addr)));

  // rvfi_mem_wdata is 32 bits wide, but we only check the bytes masked by mem_wmask
  rvfi_mem_wdata_0_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_wmask[0])|-> (rvfi_rm.mem_wdata[7:0] == rvfi_core.mem_wdata[7:0]))
    else `uvm_error("RVFI_MEM_WDATA", $sformatf("MISMATCH PC: %0h rvfi_rm.mem_wdata=%0h rvfi_core.mem_wdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_wdata), $sampled(rvfi_core.mem_wdata)));

  rvfi_mem_wdata_1_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_wmask[1])|-> (rvfi_rm.mem_wdata[15:8] == rvfi_core.mem_wdata[15:8]))
    else `uvm_error("RVFI_MEM_WDATA", $sformatf("MISMATCH PC: %0h rvfi_rm.mem_wdata=%0h rvfi_core.mem_wdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_wdata), $sampled(rvfi_core.mem_wdata)));
  
  rvfi_mem_wdata_2_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_wmask[2])|-> (rvfi_rm.mem_wdata[23:16] == rvfi_core.mem_wdata[23:16]))
    else `uvm_error("RVFI_MEM_WDATA", $sformatf("MISMATCH PC: %0h rvfi_rm.mem_wdata=%0h rvfi_core.mem_wdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_wdata), $sampled(rvfi_core.mem_wdata)));

  rvfi_mem_wdata_3_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_wmask[3])|-> (rvfi_rm.mem_wdata[31:24] == rvfi_core.mem_wdata[31:24]))
    else `uvm_error("RVFI_MEM_WDATA", $sformatf("MISMATCH PC: %0h rvfi_rm.mem_wdata=%0h rvfi_core.mem_wdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_wdata), $sampled(rvfi_core.mem_wdata)));


  // rvfi_mem_rdata
  rvfi_mem_rdata_0_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_rmask[0])|-> (rvfi_rm.mem_rdata[7:0] == rvfi_core.mem_rdata[7:0]))
    else `uvm_error("RVFI_MEM_RDATA", $sformatf("MISMATCH PC %0h rvfi_rm.mem_rdata=%0h rvfi_core.mem_rdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_rdata[7:0]), $sampled(rvfi_core.mem_rdata[7:0])));

  rvfi_mem_rdata_1_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_rmask[1])|-> (rvfi_rm.mem_rdata[15:8] == rvfi_core.mem_rdata[15:8]))
    else `uvm_error("RVFI_MEM_RDATA", $sformatf("MISMATCH PC %0h rvfi_rm.mem_rdata=%0h rvfi_core.mem_rdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_rdata[15:8]), $sampled(rvfi_core.mem_rdata[15:8])));

  rvfi_mem_rdata_2_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_rmask[2])|-> (rvfi_rm.mem_rdata[23:16] == rvfi_core.mem_rdata[23:16]))
    else `uvm_error("RVFI_MEM_RDATA", $sformatf("MISMATCH PC %0h rvfi_rm.mem_rdata=%0h rvfi_core.mem_rdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_rdata[23:16]), $sampled(rvfi_core.mem_rdata[23:16])));

  rvfi_mem_rdata_3_a: assert property(@ (posedge rvfi_core.clk)
    rvfi_rm.valid and (rvfi_core.mem_rmask[3])|-> (rvfi_rm.mem_rdata[31:24] == rvfi_core.mem_rdata[31:24]))
    else `uvm_error("RVFI_MEM_RDATA", $sformatf("MISMATCH PC %0h rvfi_rm.mem_rdata=%0h rvfi_core.mem_rdata=%0h",$sampled(rvfi_core.pc_rdata), $sampled(rvfi_rm.mem_rdata[31:24]), $sampled(rvfi_core.mem_rdata[31:24])));


endmodule

`endif // __RVFI_COMPARE_SVA_SV__