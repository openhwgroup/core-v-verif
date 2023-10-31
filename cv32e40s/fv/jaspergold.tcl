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

  # Message Severities
  ## Error on file not found
  set_message -error WNL074
  ## Allow omitted param defaults
  set_message -info VERI-1818
  ## Allow parameter treated as localparam
  set_message -info VERI-2418
  ## Allow empty port in module declaration
  set_message -info VERI-8026
  ## Allow multiplier blackboxing
  set_message -info WNL018

  # Analyze & Elaborate
  analyze  -sv12  -f fv.flist
  elaborate  -top uvmt_cv32e40s_tb  -extract_covergroup

  # Clock & Reset
  clock  clknrst_if.clk
  reset  ~clknrst_if.reset_n

  # Assumes
  assume  -from_assert  {*_memory_assert_i.u_assert.a_r_after_a}
  assume  -from_assert  {*.obi_*_memory_assert_i.*.a_*par}
  assume  -from_assert  {*integration_assert_i.a_stable_*}
  assume  -from_assert  {*integration_assert_i.a_aligned_*}
  assume  -from_assert  {*integration_assert_i.a_no_scan_cg}
}

cvfv_rerun
