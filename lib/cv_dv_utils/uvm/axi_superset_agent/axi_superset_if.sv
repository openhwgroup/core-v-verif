// ----------------------------------------------------------------------------
// Copyright 2023 CEA*
// *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//[END OF HEADER]
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//  Description : ACE-lite Interface
// ----------------------------------------------------------------------------

interface axi_superset_if (
  input logic clk_i,
  input logic reset_n
);

  import axi_superset_pkg::*;

  axi_dv_ver_t axi_version ;

  // ------------------------------------------------------------------------
  // AW Channel
  // ------------------------------------------------------------------------
  // From AXI4 Protocol
  axi_sig_id_t         aw_id          ;
  axi_sig_addr_t       aw_addr        ;
  axi_sig_len_t        aw_len         ;
  axi_sig_size_t       aw_size        ;
  axi_sig_burst_t      aw_burst       ;
  axi_sig_lock_t       aw_lock        ;
  axi_sig_cache_t      aw_cache       ;
  axi_sig_prot_t       aw_prot        ;
  axi_sig_qos_t        aw_qos         ;
  axi_sig_region_t     aw_region      ;
  axi_sig_user_t       aw_user        ;
  // Additional signals from AXI5 protocol
  axi_sig_atop_t       aw_atop        ;
  logic                aw_trace       ;
  axi_sig_loop_t       aw_loop        ;
  logic                aw_mmusecsid   ;
  axi_sig_mmusid_t     aw_mmusid      ;
  logic                aw_mmussidv    ;
  axi_sig_mmussid_t    aw_mmussid     ;
  logic                aw_mmuatst     ;
  axi_sig_nsaid_t      aw_nsaid       ;
  logic                aw_idunq       ;
  // Control signals
  logic                aw_valid       ;
  logic                aw_ready       ;

    /* pragma translate_off */

  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready ) -> !$isunknown( aw_id          ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready ) -> !$isunknown( aw_addr        ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready ) -> !$isunknown( aw_len         ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready ) -> !$isunknown( aw_size        ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready ) -> !$isunknown( aw_burst       ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready ) -> !$isunknown( aw_lock        ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready ) -> !$isunknown( aw_cache       ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready ) -> !$isunknown( aw_prot        ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready ) -> !$isunknown( aw_qos         ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready ) -> !$isunknown( aw_region      ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready ) -> !$isunknown( aw_user        ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready && ( axi_version != AXI4 ) ) -> !$isunknown( aw_atop        ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready && ( axi_version != AXI4 ) ) -> !$isunknown( aw_trace       ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready && ( axi_version != AXI4 ) ) -> !$isunknown( aw_loop        ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready && ( axi_version != AXI4 ) ) -> !$isunknown( aw_mmusecsid   ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready && ( axi_version != AXI4 ) ) -> !$isunknown( aw_mmusid      ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready && ( axi_version != AXI4 ) ) -> !$isunknown( aw_mmussidv    ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready && ( axi_version != AXI4 ) ) -> !$isunknown( aw_mmussid     ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready && ( axi_version != AXI4 ) ) -> !$isunknown( aw_mmuatst     ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready && ( axi_version != AXI4 ) ) -> !$isunknown( aw_nsaid       ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( aw_valid && aw_ready && ( axi_version != AXI4 ) ) -> !$isunknown( aw_idunq       ) );

  /* pragma translate_on */


  // ------------------------------------------------------------------------
  // W Channel
  // ------------------------------------------------------------------------
  // From AXI4 Protocol
  axi_sig_data_t      w_data    ;
  axi_sig_wstrb_t     w_strb    ;
  logic               w_last    ;
  axi_sig_user_t      w_user    ;
  // Additional signals from AXI5 protocol
  axi_sig_datachk_t   w_datachk ;
  axi_sig_poison_t    w_poison  ;
  logic               w_trace   ;
  // Control signals
  logic               w_valid   ;
  logic               w_ready   ;

  /* pragma translate_off */

  assert property ( @(posedge clk_i) disable iff(!reset_n) ( w_valid && w_ready ) -> !$isunknown( w_data    ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( w_valid && w_ready ) -> !$isunknown( w_strb    ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( w_valid && w_ready ) -> !$isunknown( w_last    ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( w_valid && w_ready ) -> !$isunknown( w_user    ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( w_valid && w_ready && ( axi_version != AXI4 ) ) -> !$isunknown( w_datachk ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( w_valid && w_ready && ( axi_version != AXI4 ) ) -> !$isunknown( w_poison  ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( w_valid && w_ready && ( axi_version != AXI4 ) ) -> !$isunknown( w_trace   ) );

  /* pragma translate_on */

  // ------------------------------------------------------------------------
  // B Channel
  // ------------------------------------------------------------------------
  // From AXI4 Protocol
  axi_sig_id_t        b_id    ;
  axi_sig_resp_t      b_resp  ;
  axi_sig_user_t      b_user  ;
  // Additional signals from AXI5 protocol
  logic               b_trace ;
  axi_sig_loop_t      b_loop  ;
  logic               b_idunq ;
  // Control signals
  logic               b_valid ;
  logic               b_ready ;

  /* pragma translate_off */

  assert property ( @(posedge clk_i) disable iff(!reset_n) ( b_valid && b_ready ) -> !$isunknown( b_id    ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( b_valid && b_ready ) -> !$isunknown( b_resp  ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( b_valid && b_ready ) -> !$isunknown( b_user  ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( b_valid && b_ready && ( axi_version != AXI4 ) ) -> !$isunknown( b_trace ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( b_valid && b_ready && ( axi_version != AXI4 ) ) -> !$isunknown( b_loop  ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( b_valid && b_ready && ( axi_version != AXI4 ) ) -> !$isunknown( b_idunq ) );

  /* pragma translate_on */

  // ------------------------------------------------------------------------
  // AR Channel
  // ------------------------------------------------------------------------
  // From AXI4 Protocol
  axi_sig_id_t        ar_id        ;
  axi_sig_addr_t      ar_addr      ;
  axi_sig_len_t       ar_len       ;
  axi_sig_size_t      ar_size      ;
  axi_sig_burst_t     ar_burst     ;
  axi_sig_lock_t      ar_lock      ;
  axi_sig_cache_t     ar_cache     ;
  axi_sig_prot_t      ar_prot      ;
  axi_sig_qos_t       ar_qos       ;
  axi_sig_region_t    ar_region    ;
  axi_sig_user_t      ar_user      ;
  // Additional signals from AXI5 protocol
  logic               ar_trace     ;
  axi_sig_loop_t      ar_loop      ;
  logic               ar_mmusecsid ;
  axi_sig_mmusid_t    ar_mmusid    ;
  logic               ar_mmussidv  ;
  axi_sig_mmussid_t   ar_mmussid   ;
  logic               ar_mmuatst   ;
  axi_sig_nsaid_t     ar_nsaid     ;
  logic               ar_idunq     ;
  // Control signals
  logic               ar_valid     ;
  logic               ar_ready     ;

      /* pragma translate_off */

  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready ) -> !$isunknown( ar_id        ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready ) -> !$isunknown( ar_addr      ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready ) -> !$isunknown( ar_len       ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready ) -> !$isunknown( ar_size      ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready ) -> !$isunknown( ar_burst     ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready ) -> !$isunknown( ar_lock      ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready ) -> !$isunknown( ar_cache     ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready ) -> !$isunknown( ar_prot      ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready ) -> !$isunknown( ar_qos       ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready ) -> !$isunknown( ar_region    ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready ) -> !$isunknown( ar_user      ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready && ( axi_version != AXI4 ) ) -> !$isunknown( ar_trace     ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready && ( axi_version != AXI4 ) ) -> !$isunknown( ar_loop      ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready && ( axi_version != AXI4 ) ) -> !$isunknown( ar_mmusecsid ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready && ( axi_version != AXI4 ) ) -> !$isunknown( ar_mmusid    ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready && ( axi_version != AXI4 ) ) -> !$isunknown( ar_mmussidv  ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready && ( axi_version != AXI4 ) ) -> !$isunknown( ar_mmussid   ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready && ( axi_version != AXI4 ) ) -> !$isunknown( ar_mmuatst   ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready && ( axi_version != AXI4 ) ) -> !$isunknown( ar_nsaid     ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( ar_valid && ar_ready && ( axi_version != AXI4 ) ) -> !$isunknown( ar_idunq     ) );

  /* pragma translate_on */

  // ------------------------------------------------------------------------
  // R Channel
  // ------------------------------------------------------------------------
  // From AXI4 Protocol
  axi_sig_id_t        r_id      ;
  axi_sig_data_t      r_data    ;
  axi_sig_resp_t      r_resp    ;
  logic               r_last    ;
  axi_sig_user_t      r_user    ;
  // Additional signals from AXI5 protocol
  axi_sig_datachk_t   r_datachk ;
  axi_sig_poison_t    r_poison  ;
  logic               r_trace   ;
  axi_sig_loop_t      r_loop    ;
  logic               r_idunq   ;
  // Control signals
  logic               r_valid   ;
  logic               r_ready   ;

    /* pragma translate_off */

  assert property ( @(posedge clk_i) disable iff(!reset_n) ( r_valid && r_ready ) -> !$isunknown( r_id      ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( r_valid && r_ready ) -> !$isunknown( r_data    ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( r_valid && r_ready ) -> !$isunknown( r_resp    ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( r_valid && r_ready ) -> !$isunknown( r_last    ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( r_valid && r_ready ) -> !$isunknown( r_user    ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( r_valid && r_ready && ( axi_version != AXI4 ) ) -> !$isunknown( r_datachk ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( r_valid && r_ready && ( axi_version != AXI4 ) ) -> !$isunknown( r_poison  ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( r_valid && r_ready && ( axi_version != AXI4 ) ) -> !$isunknown( r_trace   ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( r_valid && r_ready && ( axi_version != AXI4 ) ) -> !$isunknown( r_loop    ) );
  assert property ( @(posedge clk_i) disable iff(!reset_n) ( r_valid && r_ready && ( axi_version != AXI4 ) ) -> !$isunknown( r_idunq   ) );

  /* pragma translate_on */

  // task to wait a specific number of clock cycle
  task automatic wait_n_clock_cycle( int unsigned n_clock_cycle );
    for (int i = 0 ; i < n_clock_cycle ; i++) begin
      @(posedge clk_i);
    end
  endtask
endinterface
