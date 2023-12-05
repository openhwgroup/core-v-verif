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
//  Description : To config the response 
//                
// 
// ----------------------------------------------------------------------------

class memory_rsp_cfg  extends uvm_object;



    //////////////////////////////////////////////////////
    //Configuration Parameters
    /////////////////////////////////////////////////////
    // Enable the memory response model (mrm) 
    rand bit                 m_enable;       // is the response model enabled

    // --------------------------------------------------
    // Set the order of the response 
    // IN_ORDER_RSP, 
    // OUT_OF_ORDER_RSP, 
    // INVERSE_ORDER_RSP
    // --------------------------------------------------
    rand memory_rsp_order_t  rsp_order;      // order of the response 

    // --------------------------------------------------
    // Set the delay between the responses
    // NORMAL_RSP      (random delay)
    // ZERO_DELAY_RSP  (responses without any delay between them)
    // FIXED_DELAY_RSP (A fixed delay define by inter_data_cycle_fixed_delay)
    // --------------------------------------------------
    rand memory_rsp_mode_t   rsp_mode;       // mode of the rsp 

    // --------------------------------------------------
    // FIXED_DELAY_RSP (A fixed delay define by inter_data_cycle_fixed_delay)
    // --------------------------------------------------
    rand int unsigned         inter_data_cycle_fixed_delay;

    // ---------------------------------------------------------------------
    // Following variables are used to enable the insertion of errors
    // If enabled the mrm may respond with an error once every 100th transaction  
    // --------------------------------------------------------------------
    rand bit                insert_wr_error; 
    rand bit                insert_rd_error; 
    rand bit                insert_amo_wr_error; 
    rand bit                insert_amo_rd_error; 
    rand bit                insert_wr_exclusive_fail; 
    rand bit                insert_rd_exclusive_fail; 
    rand bit                unsolicited_rsp; 

    // ---------------------------------------------------------------------
    // These variables fix the maximum number of errors that can be inserted 
    // if that error type is enabled 
    // --------------------------------------------------------------------
    rand int unsigned        num_rd_errors;
    rand int unsigned        num_wr_errors;
    rand int unsigned        num_amo_rd_errors;
    rand int unsigned        num_amo_wr_errors;
    rand int unsigned        num_rd_exclusive_fails;
    rand int unsigned        num_wr_exclusive_fails;

    // ---------------------------------------------------------------------
    // 
    // Configuration variable to be passed to interface to generate internal
    // ready signal. This is only relevant if user connects the internally
    // generated ready signal
    // This controls the back pressure of incoming requests 
    // --------------------------------------------------------------------
    rand bp_t               m_bp; 

    // ------------------------------------------------------------------------
     // Utilities for the variables
     // FIXME: Add missing variables 
     // ------------------------------------------------------------------------
    `uvm_object_utils_begin( memory_rsp_cfg )
        `uvm_field_int( m_enable,                             UVM_DEFAULT | UVM_BIN)
        `uvm_field_enum(memory_rsp_order_t, rsp_order,        UVM_DEFAULT | UVM_ENUM)
        `uvm_field_enum(memory_rsp_mode_t,  rsp_mode,         UVM_DEFAULT | UVM_ENUM)
        `uvm_field_int( insert_rd_error,                      UVM_DEFAULT | UVM_BIN)
        `uvm_field_int( insert_wr_error,                      UVM_DEFAULT | UVM_BIN)
        `uvm_field_int( insert_rd_exclusive_fail,             UVM_DEFAULT | UVM_BIN)
        `uvm_field_int( insert_wr_exclusive_fail,             UVM_DEFAULT | UVM_BIN)
        `uvm_field_int( insert_amo_rd_error,                  UVM_DEFAULT | UVM_BIN)
        `uvm_field_int( insert_amo_wr_error,                  UVM_DEFAULT | UVM_BIN)
        `uvm_field_int( inter_data_cycle_fixed_delay,         UVM_DEFAULT | UVM_UNSIGNED)
        `uvm_field_int( num_rd_errors,                        UVM_DEFAULT | UVM_UNSIGNED)
        `uvm_field_int( num_wr_errors,                        UVM_DEFAULT | UVM_UNSIGNED)
        `uvm_field_int( num_amo_rd_errors,                    UVM_DEFAULT | UVM_UNSIGNED)
        `uvm_field_int( num_amo_rd_errors,                    UVM_DEFAULT | UVM_UNSIGNED)
    `uvm_object_utils_end

    function new( string name ="" );
        super.new( name );
    endfunction

    // -------------------------------------------
    // Constraints by default
    // if users want to have different constraints 
    // they have to disable following constraints
    // -------------------------------------------

    constraint memory_rsp_mode_c { 
           rsp_mode dist {NORMAL_RSP:= 90, ZERO_DELAY_RSP :=7, FIXED_DELAY_RSP := 1};
    }
    constraint memory_rsp_order_zer_delay_c {
      rsp_mode == ZERO_DELAY_RSP -> {
             rsp_order dist {IN_ORDER_RSP:= 50, INVERSE_ORDER_RSP:=50, OUT_OF_ORDER_RSP:= 0};
      } 
      rsp_mode == FIXED_DELAY_RSP -> { 
             rsp_order dist {IN_ORDER_RSP:= 100, INVERSE_ORDER_RSP:=0, OUT_OF_ORDER_RSP:= 0};
      } 
      rsp_mode == NORMAL_RSP -> {
             rsp_order dist {IN_ORDER_RSP:= 33, INVERSE_ORDER_RSP:=33, OUT_OF_ORDER_RSP:= 33}; 
      }
    }

    // ------------------------------------------------------------------------
    // Constraint to add more intra-data idle cycles
    // ------------------------------------------------------------------------
    constraint  inter_data_cycle_fixed_delay_c {inter_data_cycle_fixed_delay dist {0 := 75, [1:50] := 15, [50:100] := 9, [100:500] := 1};};
    
    constraint  bp_type_c { 
           m_bp dist {NEVER:= 10, LIGHT:= 30, MEDIUM:= 40, HEAVY:= 20};
    };

    constraint rsp_mode_before_rsp_order   { solve rsp_mode before rsp_order; }
  
    
    constraint no_unsolicited_rsp_c {unsolicited_rsp == 0;};

    constraint num_rd_error_c  {(insert_rd_error == 1) -> num_rd_errors > 0;}
    constraint num_wr_error_c  {(insert_wr_error == 1) -> num_wr_errors > 0;}
    constraint num_rd_exclusive_fail_c  {(insert_rd_exclusive_fail == 1) -> num_rd_exclusive_fails > 0;}
    constraint num_wr_exclusive_fail_c  {(insert_wr_exclusive_fail == 1) -> num_wr_exclusive_fails > 0;}
    constraint num_amo_rd_error_c  {(insert_amo_rd_error == 1) -> num_amo_rd_errors > 0;}
    constraint num_amo_wr_error_c  {(insert_amo_wr_error == 1) -> num_amo_wr_errors > 0;}
    // ------------------------------------------------------------------------
    // Convert2String
    //
    // Return configuration in a pretty, one-line format
    // ------------------------------------------------------------------------
    virtual function string convert2string();
       string s = "";
       
       s = { s, $sformatf( "ENABLE=%0d, ", m_enable ) };
       s = { s, $sformatf( "RSP_ORDER=%0s, ", rsp_order.name() ) };
       s = { s, $sformatf( "RSP_MODE=%0s, ", rsp_mode.name() ) };
       s = { s, $sformatf( "INSERT_RD_ERROR=%0d, ", insert_rd_error ) };
       s = { s, $sformatf( "INSERT_WR_ERROR=%0d, ", insert_wr_error ) };
       s = { s, $sformatf( "INSERT_RD_exclusive_fail=%0d, ", insert_rd_exclusive_fail ) };
       s = { s, $sformatf( "INSERT_WR_exclusive_fail=%0d, ", insert_wr_exclusive_fail ) };
       s = { s, $sformatf( "INSERT_AMO_RD_ERROR=%0d, ", insert_amo_rd_error ) };
       s = { s, $sformatf( "INSERT_AMO_WR_ERROR=%0d, ", insert_amo_wr_error ) };
       s = { s, $sformatf( "INTER_CYCLE_DELAY=%0d, ", inter_data_cycle_fixed_delay ) };
       s = { s, $sformatf( "NUM RD ERRORS=%0d, ", num_rd_errors ) };
       s = { s, $sformatf( "NUM WR ERRORS=%0d, ", num_wr_errors ) };
       s = { s, $sformatf( "NUM AMO RD ERRORS=%0d, ", num_amo_rd_errors ) };
       s = { s, $sformatf( "NUM AMO WR ERRORS=%0d, ", num_amo_wr_errors ) };
       s = { s, $sformatf( "BP=%0s", m_bp.name() ) };
      
       return s;
    endfunction : convert2string

endclass : memory_rsp_cfg


// -----------------------------------------------------
// Derived config class withtout insertion of errors 
// -----------------------------------------------------
class memory_rsp_cfg_no_error extends memory_rsp_cfg;

    `uvm_object_utils( memory_rsp_cfg_no_error )

    function new( string name ="" );
        super.new( name );
    endfunction


    constraint no_rd_error_c      {insert_rd_error == 0;};
    constraint no_wr_error_c      {insert_wr_error == 0;};
    constraint no_rd_exclusive_fail_c      {insert_rd_exclusive_fail == 0;};
    constraint no_wr_exclusive_fail_c      {insert_wr_exclusive_fail == 0;};
    constraint no_amo_rd_error_c  {insert_amo_rd_error == 0;};
    constraint no_amo_wr_error_c  {insert_amo_wr_error == 0;};
endclass 
