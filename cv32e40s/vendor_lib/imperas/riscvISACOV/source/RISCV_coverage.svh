//
// Copyright (c) 2022 Imperas Software Ltd., www.imperas.com
// 
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
// either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.
//
//
  
`include "RISCV_coverage_config.svh" 
`include "coverage/RISCV_coverage_pkg.svh"


import RISCV_coverage_pkg::*;
 
class coverage extends RISCV_coverage;
 
    function new(virtual rvviTrace #(ILEN, XLEN, FLEN, VLEN, NHART, RETIRE) rvvi);
        super.new(rvvi);

        // Initialize custom covergroups here 

    endfunction
 
    function void sample(bit trap, int hart, int issue, string disass); 
        
        sample_extensions(trap, hart, issue, disass);

        // Sample custom covergroups here
        
    endfunction
 
endclass

