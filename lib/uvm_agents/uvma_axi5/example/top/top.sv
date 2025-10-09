// ----------------------------------------------------------------------------
//Copyright 2023 CEA*
//*Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
//
//Licensed under the Apache License, Version 2.0 (the "License");
//you may not use this file except in compliance with the License.
//You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
//Unless required by applicable law or agreed to in writing, software
//distributed under the License is distributed on an "AS IS" BASIS,
//WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//See the License for the specific language governing permissions and
//limitations under the License.
//[END OF HEADER]
// ----------------------------------------------------------------------------


module top;

  timeunit 1ns;
  timeprecision 100ps;

  import uvm_pkg::*;
  import test_pkg::*;

  bit clk_i;
  bit reset;
  bit reset_n;
  bit post_shutdown_phase;

  xrtl_clock_vif clock_if( .clock(clk_i));
  xrtl_reset_vif #(1'b1,10,0) reset_if(.clk(clk_i),
                                      .reset(reset),
                                      .reset_n(reset_n),
                                      .post_shutdown_phase(post_shutdown_phase)
                                      );

  bp_vif #(1) aw_bp   ( .clk( clk_i ), .rstn( reset_n ) );
  bp_vif #(1) w_bp    ( .clk( clk_i ), .rstn( reset_n ) );
  bp_vif #(1) b_bp    ( .clk( clk_i ), .rstn( reset_n ) );
  bp_vif #(1) ar_bp   ( .clk( clk_i ), .rstn( reset_n ) );
  bp_vif #(1) r_bp    ( .clk( clk_i ), .rstn( reset_n ) );

  uvma_axi_intf       axi_assert_if( .clk(clk_i), .rst_n(reset_n) );
//  axi_superset_if  axi_vif (.clk_i(clk_i), .reset_n(reset_n));
  uvma_axi_mst_intf   axi_vif( .clk(clk_i), .rst_n(reset_n) );
  uvma_axi_intf       axi_slv_vif( .clk(clk_i), .rst_n(reset_n) );

  assign axi_vif.aw_ready   = axi_slv_vif.aw_ready;
  assign axi_vif.w_ready  = axi_slv_vif.w_ready; 
  assign axi_vif.ar_ready = axi_slv_vif.ar_ready; 
  assign axi_vif.b_ready  = ~b_bp.bp_out ;
  assign axi_vif.r_ready  = ~r_bp.bp_out ;

  assign axi_slv_vif.b_ready  = axi_vif.b_ready ;
  assign axi_slv_vif.r_ready  = axi_vif.r_ready ;

   assign axi_slv_vif.aw_id     = axi_vif.aw_id;
   assign axi_slv_vif.aw_addr   = axi_vif.aw_addr;
   assign axi_slv_vif.aw_user   = axi_vif.aw_user;
   assign axi_slv_vif.aw_len    = axi_vif.aw_len;
   assign axi_slv_vif.aw_size   = axi_vif.aw_size;
   assign axi_slv_vif.aw_burst  = axi_vif.aw_burst;
   assign axi_slv_vif.aw_lock   = axi_vif.aw_lock;
   assign axi_slv_vif.aw_cache  = axi_vif.aw_cache;
   assign axi_slv_vif.aw_prot   = axi_vif.aw_prot;
   assign axi_slv_vif.aw_qos    = axi_vif.aw_qos;
   assign axi_slv_vif.aw_region = axi_vif.aw_region;
   assign axi_slv_vif.aw_valid   = axi_vif.aw_valid;
   assign axi_slv_vif.aw_atop    = axi_vif.aw_atop;
   assign axi_slv_vif.aw_trace   = axi_vif.aw_trace;
   assign axi_slv_vif.aw_loop    = axi_vif.aw_loop;
   assign axi_slv_vif.aw_mmusecsid   = axi_vif.aw_mmusecsid;
   assign axi_slv_vif.aw_mmusid      = axi_vif.aw_mmusid;
   assign axi_slv_vif.aw_mmussidv    = axi_vif.aw_mmussidv;
   assign axi_slv_vif.aw_mmussid     = axi_vif.aw_mmussid;
   assign axi_slv_vif.aw_mmuatst     = axi_vif.aw_mmuatst;
   assign axi_slv_vif.aw_nsaid   = axi_vif.aw_nsaid;
   assign axi_slv_vif.aw_idunq   = axi_vif.aw_idunq;


   assign axi_slv_vif.w_data     = axi_vif.w_data;
   assign axi_slv_vif.w_strb     = axi_vif.w_strb;
   assign axi_slv_vif.w_user     = axi_vif.w_user;
   assign axi_slv_vif.w_last     = axi_vif.w_last;
   assign axi_slv_vif.w_datachk  = axi_vif.w_datachk;
   assign axi_slv_vif.w_poison   = axi_vif.w_poison;
   assign axi_slv_vif.w_trace    = axi_vif.w_trace;
   assign axi_slv_vif.w_valid    = axi_vif.w_valid;


   assign axi_vif.b_id     = axi_slv_vif.b_id;
   assign axi_vif.b_user   = axi_slv_vif.b_user;
   assign axi_vif.b_resp   = axi_slv_vif.b_resp;
   assign axi_vif.b_trace  = axi_slv_vif.b_trace;
   assign axi_vif.b_loop   = axi_slv_vif.b_loop;
   assign axi_vif.b_idunq  = axi_slv_vif.b_idunq;
   assign axi_vif.b_valid  = axi_slv_vif.b_valid;


   assign axi_slv_vif.ar_id      = axi_vif.ar_id;
   assign axi_slv_vif.ar_addr    = axi_vif.ar_addr;
   assign axi_slv_vif.ar_user    = axi_vif.ar_user;
   assign axi_slv_vif.ar_len     = axi_vif.ar_len;
   assign axi_slv_vif.ar_size    = axi_vif.ar_size;
   assign axi_slv_vif.ar_burst   = axi_vif.ar_burst;
   assign axi_slv_vif.ar_lock    = axi_vif.ar_lock;
   assign axi_slv_vif.ar_cache   = axi_vif.ar_cache;
   assign axi_slv_vif.ar_prot    = axi_vif.ar_prot;
   assign axi_slv_vif.ar_qos     = axi_vif.ar_qos;
   assign axi_slv_vif.ar_region  = axi_vif.ar_region;
   assign axi_slv_vif.ar_valid   = axi_vif.ar_valid;
   assign axi_slv_vif.ar_trace   = axi_vif.ar_trace;
   assign axi_slv_vif.ar_loop    = axi_vif.ar_loop;
   assign axi_slv_vif.ar_mmusecsid   = axi_vif.ar_mmusecsid;
   assign axi_slv_vif.ar_mmusid      = axi_vif.ar_mmusid;
   assign axi_slv_vif.ar_mmussidv    = axi_vif.ar_mmussidv;
   assign axi_slv_vif.ar_mmussid     = axi_vif.ar_mmussid;
   assign axi_slv_vif.ar_mmuatst     = axi_vif.ar_mmuatst;
   assign axi_slv_vif.ar_nsaid       = axi_vif.ar_nsaid;
   assign axi_slv_vif.ar_idunq       = axi_vif.ar_idunq;


   assign axi_vif.r_id     = axi_slv_vif.r_id;
   assign axi_vif.r_data   = axi_slv_vif.r_data;
   assign axi_vif.r_user   = axi_slv_vif.r_user;
   assign axi_vif.r_resp   = axi_slv_vif.r_resp;
   assign axi_vif.r_last   = axi_slv_vif.r_last;
   assign axi_vif.r_datachk = axi_slv_vif.r_datachk;
   assign axi_vif.r_poison  = axi_slv_vif.r_poison;
   assign axi_vif.r_trace   = axi_slv_vif.r_trace;
   assign axi_vif.r_loop    = axi_slv_vif.r_loop;
   assign axi_vif.r_idunq   = axi_slv_vif.r_idunq;
   assign axi_vif.r_valid   = axi_slv_vif.r_valid;

   uvma_axi_aw_assert         axi_aw_assert(.axi_assert(axi_assert_if));
   uvma_axi_w_assert          axi_w_assert(.axi_assert(axi_assert_if));
   uvma_axi_ar_assert         axi_ar_assert(.axi_assert(axi_assert_if));
   uvma_axi_r_assert          axi_r_assert(.axi_assert(axi_assert_if));
   uvma_axi_b_assert          axi_b_assert(.axi_assert(axi_assert_if));
   uvma_axi_assert            axi_assert(.axi_assert(axi_assert_if));
   uvma_axi_amo_assert        axi_amo_assert(.axi_assert(axi_assert_if));

  initial begin
      uvm_config_db #(virtual xrtl_clock_vif )::set(uvm_root::get(), "*", "cc_clock_driver", clock_if );
      uvm_config_db #(virtual xrtl_reset_vif #( 1'b1,10,0) )::set(uvm_root::get(), "*", "cc_reset_driver", reset_if );

      uvm_config_db #(virtual bp_vif #(1) )::set(uvm_root::get(), "*", "aw_bp_agent" , aw_bp ) ;
      uvm_config_db #(virtual bp_vif #(1) )::set(uvm_root::get(), "*", "w_bp_agent"  , w_bp  ) ;
      uvm_config_db #(virtual bp_vif #(1) )::set(uvm_root::get(), "*", "b_bp_agent"  , b_bp  ) ;
      uvm_config_db #(virtual bp_vif #(1) )::set(uvm_root::get(), "*", "ar_bp_agent" , ar_bp ) ;
      uvm_config_db #(virtual bp_vif #(1) )::set(uvm_root::get(), "*", "r_bp_agent"  , r_bp  ) ;

      uvm_config_db #(virtual uvma_axi_mst_intf)::set(null,"*", "axi_mst_vif", axi_vif);
      uvm_config_db #(virtual uvma_axi_intf)::set(null,"*", "axi_vif", axi_slv_vif);

//      uvm_config_db #(virtual axi_superset_if )::set(uvm_root::get(), "*", "AXI_SUPERSET_IF",  axi_vif);

      run_test();
  end

endmodule

