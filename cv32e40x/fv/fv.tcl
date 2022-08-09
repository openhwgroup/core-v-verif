# Copyright 2022 Silicon Labs, Inc.
# Copyright 2022 OpenHW Group
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://solderpad.org/licenses/
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0


# TODO:silabs-robin  No hardcoded paths, integrate with `mk/` definitions.


proc cvfv_rerun {} {
  clear  -all

  analyze  -sv12  uvm_pkg.sv
  analyze  -sv12  defines.sv
  analyze  -sv12  -f  ../../core-v-cores/cv32e40x/cv32e40x_manifest.flist
  analyze  -sv12                                \
    +incdir+../tb/uvmt/                      \
    +incdir+../../lib/uvm_agents/uvma_rvfi   \
    +incdir+../../lib/uvm_agents/uvma_fencei \
    dummy_pkg.sv
  analyze  -sv12                                          \
    ../../lib/uvm_agents/uvma_fencei/uvma_fencei_if.sv \
    ../../lib/uvm_agents/uvma_rvfi/uvma_rvfi_instr_if.sv
  analyze  -sv12  ../tb/uvmt/uvmt_cv32e40x_tb.sv
  analyze  -sv12  ../tb/uvmt/uvmt_cv32e40x_dut_wrap.sv
  analyze  -sv12                                      \
    ../tb/uvmt/uvmt_cv32e40x_interrupt_assert.sv   \
    ../tb/uvmt/uvmt_cv32e40x_debug_assert.sv       \
    ../tb/uvmt/uvmt_cv32e40x_fencei_assert.sv      \
    ../tb/uvmt/uvmt_cv32e40x_integration_assert.sv
  analyze  -sv12  ../tb/uvmt/uvmt_cv32e40x_tb_ifs.sv

  elaborate  -top  uvmt_cv32e40x_tb

  clock  clknrst_if.clk
  reset  ~clknrst_if.reset_n
}

cvfv_rerun
