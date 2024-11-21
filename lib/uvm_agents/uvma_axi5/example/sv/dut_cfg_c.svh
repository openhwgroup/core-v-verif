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
//  Description : This class (uvm_object) holds an abstract representation of 
//                the configuration of one Slice in the RWI. 
//
//                
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

