//
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
//

`ifndef __UVMT_CV32E40S_BASE_TEST_PKG_SV__
`define __UVMT_CV32E40S_BASE_TEST_PKG_SV__

// Pre-processor macros
`include "uvmt_cv32e40s_macros.sv"

package uvmt_cv32e40s_base_test_pkg;

    import cv32e40s_pkg::*;
    import uvm_pkg::*;

    `include "uvmt_cv32e40s_base_test_constants.sv"
    `include "uvmt_cv32e40s_base_test_tdefs.sv"

endpackage : uvmt_cv32e40s_base_test_pkg

`endif // __UVMT_CV32E40S_BASE_TEST_PKG_SV__

