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
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//

`ifndef __UVMT_CV32E40S_IMPERAS_DUMMY_PKG_SV__
`define __UVMT_CV32E40S_IMPERAS_DUMMY_PKG_SV__
import uvm_pkg::*;

package rvviApiPkg;
  function int rvviRefShutdown();
    `uvm_error("ISS_DUMMY", "USE_ISS=1 set but no ISS installation is available");
    return 0;
  endfunction : rvviRefShutdown

  function void rvviRefMemoryWrite(
    int hartId,
    longint address,
    longint data,
    int size
  );
    `uvm_error("ISS_DUMMY", "USE_ISS=1 set but not ISS installation is available");
  endfunction : rvviRefMemoryWrite
endpackage : rvviApiPkg

interface rvviTrace
  #(
    parameter int NHART  = 1,
    parameter int RETIRE = 1
  );
endinterface : rvviTrace

module uvmt_cv32e40s_imperas_dv_wrap
  import uvm_pkg::*;
  #()
  (
    rvviTrace rvvi
  );

endmodule : uvmt_cv32e40s_imperas_dv_wrap

interface uvmt_imperas_dv_if_t;
  task ref_init;
    `uvm_info("ISS_DUMMY", "ref_init called from uvmt_cv32e40s_imperas_dummy_pkg.sv", UVM_LOW);
  endtask : ref_init
endinterface : uvmt_imperas_dv_if_t

`endif // __UVMT_CV32E40S_IMPERAS_DUMMY_PKG_SV__
