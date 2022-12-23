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
 

typedef enum {
    fflags,
    frm,
    fcsr,
    jvt,
    mcause,
    mip,
    mie,
    mstatus,
    mepc
} csr_name_t;

function int get_csr_val(int hart, int issue, int after, string name, string field);
    int addr = get_csr_addr(name);

    int val;
    if (after == 1) val = this.rvvi.csr[hart][issue][addr];
    else val = this.csr_prev[hart][issue][addr];

    // Todo:  Get the csr/field info from a separate data source instead of hardcoding here.
    if (name == "fcsr") begin
        case(field)
            "fflags" : val = val & 'h1f; 
            "frm": val = (val >> 5) & 'h7;
        endcase
    end
    return val;
endfunction


function int get_csr_addr (string s);
    case (s)
        "fflags"       : return 'h1;
        "frm"       : return 'h2;
        "fcsr"       : return 'h3;
        "jvt"       : return 'h17;
        "mcause"       : return 'h342;
        "mip"       : return 'h344;
        "mie"       : return 'h304;
        "mstatus"       : return 'h300;
        "mepc"       : return 'h341;
        default: begin
            $display("ERROR: SystemVerilog Functional Coverage: get_csr_addr(%0s) not found csr", s);
            $finish(-1);
        end
    endcase
endfunction
