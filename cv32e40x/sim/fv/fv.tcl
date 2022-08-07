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


proc cvfv_rerun {} {
  clear  -all

  analyze  -sv  uvm_pkg.sv
  analyze  -sv  ../../tb/uvmt/uvmt_cv32e40x_tb.sv
}

cvfv_rerun
