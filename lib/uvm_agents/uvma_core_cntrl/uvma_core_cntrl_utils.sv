//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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

`ifndef __UVMA_CORE_CNTRL_UTILS_SV__
`define __UVMA_CORE_CNTRL_UTILS_SV__

function automatic string get_isa_str(st_core_cntrl_cfg cfg);

    string rtl_isa = $sformatf("RV%-2dIM",
                        cfg.xlen);
    string rtl_isa_plus = "";
    if (cfg.ext_a_supported)       rtl_isa = {rtl_isa, "A"};
    if (cfg.ext_f_supported)       rtl_isa = {rtl_isa, "F"};
    if (cfg.ext_d_supported)       rtl_isa = {rtl_isa, "D"};
    if (cfg.ext_c_supported)       rtl_isa = {rtl_isa, "C"};

    if (cfg.ext_zba_supported)     rtl_isa_plus = {rtl_isa_plus, "_zba"};
    if (cfg.ext_zbb_supported)     rtl_isa_plus = {rtl_isa_plus, "_zbb"};
    if (cfg.ext_zbc_supported)     rtl_isa_plus = {rtl_isa_plus, "_zbc"};
    if (cfg.ext_zbs_supported)     rtl_isa_plus = {rtl_isa_plus, "_zbs"};
    if (cfg.ext_zcb_supported)     rtl_isa_plus = {rtl_isa_plus, "_zcb"};
    if (cfg.ext_zicsr_supported)     rtl_isa_plus = {rtl_isa_plus, "_zicsr"};
    if (cfg.ext_zicntr_supported)    rtl_isa_plus = {rtl_isa_plus, "_zicntr"};

    return {rtl_isa, rtl_isa_plus};

endfunction : get_isa_str

function automatic string get_priv_str(st_core_cntrl_cfg cfg);
    string rtl_priv;

    rtl_priv = "M";

    if (cfg.mode_s_supported)      rtl_priv = {rtl_priv, "S"};
    if (cfg.mode_u_supported)      rtl_priv = {rtl_priv, "U"};
    if (cfg.mode_h_supported)      rtl_priv = {rtl_priv, "HS"};

    return rtl_priv;

endfunction : get_priv_str


function bit is_ext_b_supported(st_core_cntrl_cfg cfg);

   return  (cfg.ext_zba_supported &&
            cfg.ext_zbb_supported &&
            cfg.ext_zbc_supported) ? 1 : 0;

endfunction : is_ext_b_supported

function bit[MAX_XLEN-1:0] get_misa(st_core_cntrl_cfg cfg);

   get_misa = 0;

   if (cfg.ext_a_supported)         get_misa[0] = 1;
   if (is_ext_b_supported(cfg))     get_misa[1] = 1;
   if (cfg.ext_c_supported)         get_misa[2] = 1;
   if (cfg.ext_f_supported)         get_misa[5] = 1;
   if (cfg.ext_i_supported)         get_misa[8] = 1;
   if (cfg.ext_m_supported)         get_misa[12] = 1;
   if (cfg.mode_s_supported)        get_misa[18] = 1;
   if (cfg.mode_u_supported)        get_misa[20] = 1;

   return get_misa;

endfunction : get_misa

`endif
