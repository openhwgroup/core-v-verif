// Copyright 2023 OpenHW Group
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

`ifndef __UVMC_RVFI_REFERENCE_MODEL_UTILS_SV__
`define __UVMC_RVFI_REFERENCE_MODEL_UTILS_SV__

    function automatic string rvfi_get_isa_str(st_core_cntrl_cfg core_cfg);

        string rtl_isa = $sformatf("RV%-2dIM",
                            core_cfg.xlen);
        if (core_cfg.ext_a_supported)       rtl_isa = {rtl_isa, "A"};
        if (core_cfg.ext_f_supported)       rtl_isa = {rtl_isa, "F"};
        if (core_cfg.ext_d_supported)       rtl_isa = {rtl_isa, "D"};
        if (core_cfg.ext_c_supported)       rtl_isa = {rtl_isa, "C"};
        if (core_cfg.ext_zba_supported)     rtl_isa = {rtl_isa, "_zba"};
        if (core_cfg.ext_zbb_supported)     rtl_isa = {rtl_isa, "_zbb"};
        if (core_cfg.ext_zbc_supported)     rtl_isa = {rtl_isa, "_zbc"};
        if (core_cfg.ext_zbs_supported)     rtl_isa = {rtl_isa, "_zbs"};
        if (core_cfg.ext_zcb_supported)     rtl_isa = {rtl_isa, "_zcb"};
        if (core_cfg.ext_zicsr_supported)     rtl_isa = {rtl_isa, "_zicsr"};
        if (core_cfg.ext_zicntr_supported)     rtl_isa = {rtl_isa, "_zicntr"};

        return rtl_isa;

    endfunction : rvfi_get_isa_str

    function automatic string rvfi_get_priv_str(st_core_cntrl_cfg core_cfg);
        string rtl_priv;

        rtl_priv = "M";

        if (core_cfg.mode_s_supported)      rtl_priv = {rtl_priv, "S"};
        if (core_cfg.mode_u_supported)      rtl_priv = {rtl_priv, "U"};

        return rtl_priv;

    endfunction : rvfi_get_priv_str

`endif
