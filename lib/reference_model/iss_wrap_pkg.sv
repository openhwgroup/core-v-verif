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

`ifndef __ISS_WRAP_PKG_SV
`define __ISS_WRAP_PKG_SV

package iss_wrap_pkg;

import uvma_rvfi_pkg::*;

import "DPI-C" function int spike_create(string filename);

import "DPI-C" function void spike_set_param_uint64_t(string base, string name, longint unsigned value);
import "DPI-C" function void spike_set_param_str(string base, string name, string value);
import "DPI-C" function void spike_set_default_params(string profile);

import "DPI-C" function void spike_step_svLogic(inout vector_rvfi core, inout vector_rvfi reference_model);
import "DPI-C" function void spike_step_struct(inout st_rvfi core, inout st_rvfi reference_model);

import "DPI-C" function bit  spike_interrupt(int unsigned mip, int unsigned mie, int unsigned revert_steps, bit interrupt_allowed);
import "DPI-C" function void spike_revert_state(int num_steps);

import "DPI-C" function bit spike_set_debug(bit debug_req, int unsigned revert_steps, bit debug_allowed);


    function automatic void iss_init(string binary);

        string rtl_isa;
        string rtl_priv;

        rtl_isa = "rv32imc_zicsr_zifencei_zca_zcb_zcmp_zcmt_zba_zbb_zbc_zbs";
        rtl_priv = "MU";

        // CV32E40S hardcodes MISA bit 23(non-standard extension) to 1
        // We add "xdummy" so spike also enables bit 23 of MISA
        rtl_isa = {rtl_isa, "_xdummy"};

        //spike_init(binary);
        void'(spike_set_default_params("cv32e40s"));
        void'(spike_set_param_uint64_t("/top/core/0/", "boot_addr", 'h00000080));
        void'(spike_set_param_str("/top/", "isa", rtl_isa));
        void'(spike_set_param_str("/top/", "priv", rtl_priv));
        void'(spike_set_param_str("/top/core/0/", "isa", rtl_isa));
        void'(spike_set_param_str("/top/core/0/", "priv", rtl_priv));
        void'(spike_create(binary));
    endfunction

    function automatic st_rvfi iss_step();
        union_rvfi u_core;
        union_rvfi u_reference_model;
        bit [0:ST_NUM_WORDS-1][63:0] a_core;
        bit [0:ST_NUM_WORDS-1][63:0] a_reference_model;

        spike_step_svLogic(a_core, a_reference_model);

        foreach(a_reference_model[i]) begin
            u_reference_model.array[i] = a_reference_model[ST_NUM_WORDS-1-i];
        end

        return u_reference_model.rvfi;

    endfunction

    //Sets mip in Spike and steps one time to apply the state changes
    //This step does not step through an instruction, so iss_step() must be 
    //called to step through the first instruction of the trap handler.
    //Returns true if the interrupt can be taken, and false if CSRs cause the interrupt to not be taken
    function automatic logic iss_intr(bit [31:0] irq, bit [31:0] mie, logic interrupt_allowed, int num_revert_steps);
        logic interrupt_taken;
        
        interrupt_taken = spike_interrupt(irq, mie, num_revert_steps, interrupt_allowed);

        return interrupt_taken;
    endfunction

    function automatic logic iss_set_debug(bit debug_req, int revert_steps, bit debug_allowed);
        logic debug_taken;
        debug_taken =  spike_set_debug(debug_req, revert_steps, debug_allowed);
        return debug_taken;
    endfunction

    function automatic void iss_revert_state(int num_steps);
        spike_revert_state(num_steps);
    endfunction

endpackage : iss_wrap_pkg

`endif // __ISS_WRAP_PKG_SV
