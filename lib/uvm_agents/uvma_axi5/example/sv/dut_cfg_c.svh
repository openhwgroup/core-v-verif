// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//                                CEA - LETI
//    Reproduction and Communication of this document is strictly prohibited
//      unless specifically authorized in writing by CEA - LETI.
// ----------------------------------------------------------------------------
//                        LETI / DACLE / LISAN
// ----------------------------------------------------------------------------
// 
// 
//  File        : dut_cfg_c
// 
//  Description : This class (uvm_object) holds an abstract representation of 
//                the configuration of one Slice in the RWI. 
//
//                
// 
//  Copyright (C) 2017,2018 CEA-Leti
//  Author      : Tanuj Khandelwal 
// 
//  Id          : $Id$
//  Date        : $Date$
//  Revision    : $Rev$
// 
// ----------------------------------------------------------------------------

class dut_cfg_c extends uvm_object;

  rand bp_type_t  aw_bp ;
  rand bp_type_t  w_bp  ;
  rand bp_type_t  b_bp  ;
  rand bp_type_t  ar_bp ;
  rand bp_type_t  r_bp  ;

    `uvm_object_utils_begin( dut_cfg_c )
       `uvm_field_enum( bp_type_t, aw_bp , UVM_DEFAULT )
       `uvm_field_enum( bp_type_t, w_bp  , UVM_DEFAULT )
       `uvm_field_enum( bp_type_t, b_bp  , UVM_DEFAULT )
       `uvm_field_enum( bp_type_t, ar_bp , UVM_DEFAULT )
       `uvm_field_enum( bp_type_t, r_bp  , UVM_DEFAULT )
    `uvm_object_utils_end

    // ------------------------------------------------------------------------
    // Constructor
    // ------------------------------------------------------------------------
    function new( string name = "dut_cfg_c" );
       super.new(name);
    endfunction: new

    constraint  aw_bp_data_c { aw_bp dist { OCCASSIONAL_BP := 90, HEAVY_BP := 10};};
    constraint  w_bp_data_c  { w_bp  dist { OCCASSIONAL_BP := 90, HEAVY_BP := 10};};
    constraint  b_bp_data_c  { b_bp  dist { OCCASSIONAL_BP := 90, HEAVY_BP := 10};};
    constraint  ar_bp_data_c { ar_bp dist { OCCASSIONAL_BP := 90, HEAVY_BP := 10};};
    constraint  r_bp_data_c  { r_bp  dist { OCCASSIONAL_BP := 90, HEAVY_BP := 10};};
 
endclass : dut_cfg_c

