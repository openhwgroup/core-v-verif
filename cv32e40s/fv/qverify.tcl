# Copyright 2022 Silicon Labs, Inc.
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
# not use this file except in compliance with the License, or, at your option,
# the Apache License version 2.0.
#
# You may obtain a copy of the License at
# https://solderpad.org/licenses/SHL-2.1/
#
# Unless required by applicable law or agreed to in writing, any work
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#
# See the License for the specific language governing permissions and
# limitations under the License.


proc cvfv_rerun {} {
  onerror  {exit 1}

  # TODO:silabs-robin  Bring up the formal view before executing the rest

  puts "cvfv: compiling verilog"
  vlog  -mfcu  -f fv.flist

  puts "cvfv: initializing clock/reset"
  netlist clock "clknrst_if.clk"
  netlist reset "clknrst_if.reset_n" -active_low -async
  formal init -inferred
  formal init {clknrst_if.reset_n = 1; ##1 clknrst_if.reset_n = 0; ##2}

  puts "cvfv: compiling formal model"
  formal  compile  -d uvmt_cv32e40s_tb  -work work

  puts "cvfv: see the visualizer log for compilation warnings"
}

cvfv_rerun
