

`ifndef __ISS_WRAP_PKG_SV
`define __ISS_WRAP_PKG_SV

package iss_wrap_pkg;

import uvma_rvfi_pkg::*;

import "DPI-C" function int spike_create(string filename);

import "DPI-C" function void spike_set_param_uint64_t(string base, string name, longint unsigned value);
import "DPI-C" function void spike_set_param_str(string base, string name, string value);
import "DPI-C" function void spike_set_default_params(string profile);

import "DPI-C" function void spike_step_svOpenArray(inout bit [63:0] core[], inout bit [63:0] reference_model[]);
import "DPI-C" function void spike_step_struct(inout st_rvfi core, inout st_rvfi reference_model);


    function automatic void iss_init(string binary);

        string rtl_isa;
        string rtl_priv;

        rtl_isa = "rv32im_zicsr_zifencei_zca_zcb_zcmp_zcmt_zba_zbb_zbc_zbs";
        rtl_priv = "M";
        //spike_init(binary);
        void'(spike_set_default_params("cva6"));
        void'(spike_set_param_uint64_t("/top/core/0/", "boot_addr", 'h00000080));
        void'(spike_set_param_str("/top/", "isa", rtl_isa));
        void'(spike_set_param_str("/top/", "priv", rtl_priv));
        void'(spike_set_param_str("/top/core/0/", "isa", rtl_isa));
        void'(spike_set_param_str("/top/core/0/", "priv", rtl_priv));
        void'(spike_create(binary));
    endfunction

    function automatic void iss_step(ref st_rvfi s_reference_model);
            union_rvfi u_core;
            union_rvfi u_reference_model;
            bit [63:0] a_core [`ST_NUM_WORDS-1:0];
            bit [63:0] a_reference_model [`ST_NUM_WORDS-1:0];

            foreach(u_core.array[i]) begin
                a_core[i] = u_core.array[i];
            end

            spike_step_svOpenArray(a_core, a_reference_model);

            a_reference_model.reverse(); // foreach seems to be reversed. Quickfix to get the right order
            foreach(a_reference_model[i]) begin
                u_reference_model.array[i] = a_reference_model[i];
            end

            s_reference_model = u_reference_model.rvfi;

    endfunction

endpackage : iss_wrap_pkg

`endif // __ISS_WRAP_PKG_SV
