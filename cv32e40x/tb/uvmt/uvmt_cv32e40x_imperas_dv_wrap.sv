//
// Copyright 2022 OpenHW Group
// Copyright 2022 Imperas
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
//

`ifndef __UVMT_CV32E40X_IMPERAS_DV_WRAP_SV__
`define __UVMT_CV32E40X_IMPERAS_DV_WRAP_SV__

/**
 * Module wrapper for Imperas DV.
 */
module uvmt_cv32e40x_imperas_dv_wrap
  import uvm_pkg::*;
  #(
   )

   (
    RVVI_VLG  rvvi // RVVI SystemVerilog Interface
   );

   VLG2API       #(.CMP_PC      (1),
                   .CMP_INS     (1),
                   .CMP_GPR     (1),
                   .CMP_FPR     (0),
                   .CMP_VR      (0),
                   .CMP_CSR     (1),
                   .MISCOMPARES (1)
                 )
                 vlg2api(rvvi);

   VLG2LOG       vlg2log(rvvi);


endmodule : uvmt_cv32e40x_imperas_dv_wrap

`endif // __UVMT_CV32E40X_IMPERAS_DV_WRAP_SV__

