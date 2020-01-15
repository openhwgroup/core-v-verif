//----------------------------------------------------------------------
// Copyright 2018 Cadence Design Systems, Inc.
// Copyright 2018 NVIDIA Corporation
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

//------------------------------------------------------------------------------
//
// MACROS for resource usage
//
// Provides a set of macros which are useful for interacting with the
// resource database.
//
//------------------------------------------------------------------------------

`ifndef UVM_RESOURCE_DEFINES_SVH
`define UVM_RESOURCE_DEFINES_SVH

// m_uvm_resource_read
// -------------------
// Casts ~RSRC~ to uvm_resource#(TYPE) and if successful
// reads the resource into ~VAL~ with accessor ~OBJ~.
//
// ~SUCCESS~ shall be set to true if the resource was succesfully
// read, false otherwise.

`define uvm_resource_read(SUCCESS, RSRC, TYPE, VAL, OBJ=null)   \
begin                                                           \
  uvm_resource#(TYPE) __tmp_rsrc__;                             \
  SUCCESS = $cast(__tmp_rsrc__, RSRC);                          \
  if (SUCCESS) begin                                            \
    VAL = __tmp_rsrc__.read(OBJ);                               \
  end                                                           \
end                                                             

// uvm_resource_builtin_int_read
// -----------------------------
// Attempts to read an integral typed resource ~RSRC~
// into VAL.
//
// ~SUCCESS~ shall be set to true if the resource was succesfully
// read, false otherwise.
//
// Supported Types:
// - uvm_integral_t
// - uvm_bitstream_t
// - int
// - int unsigned
//

`define uvm_resource_builtin_int_read(SUCCESS, RSRC, VAL, OBJ=null) \
begin                                                               \
  `uvm_resource_read(SUCCESS, RSRC, uvm_integral_t, VAL, OBJ)                \
  if (!SUCCESS)                                                     \
    `uvm_resource_read(SUCCESS, RSRC, uvm_bitstream_t, VAL, OBJ)             \
  if (!SUCCESS)                                                     \
    `uvm_resource_read(SUCCESS, RSRC, int, VAL, OBJ)                         \
  if (!SUCCESS)                                                     \
    `uvm_resource_read(SUCCESS, RSRC, int unsigned, VAL, OBJ)                \
end

// uvm_resource_int_read
// ---------------------
// Attempts to read an integral typed resource ~RSRC~,
// starting with ~TYPE~ before checking the builtin types.
//
// ~SUCCESS~ shall be set to true if the resource was succesfully
// read, false otherwise.
//

`define uvm_resource_int_read(SUCCESS, RSRC, TYPE, VAL, OBJ=null) \
begin                                                             \
  `uvm_resource_read(SUCCESS, RSRC, TYPE, VAL, OBJ)               \
  if (!SUCCESS)                                                   \
    `uvm_resource_builtin_int_read(SUCCESS, RSRC, VAL, OBJ)       \
end

// uvm_resource_enum_read
// ---------------------
// Attempts to read an integral typed resource ~RSRC~,
// starting with ~TYPE~ and string before checking the 
// builtin intergral types.
//
// ~SUCCESS~ shall be set to true if the resource was succesfully
// read, false otherwise.
//

`define uvm_resource_enum_read(SUCCESS, RSRC, TYPE, VAL, OBJ=null) \
begin                                                              \
  `uvm_resource_read(SUCCESS, RSRC, TYPE, VAL, OBJ)                \
  if (!SUCCESS) begin                                              \
    TYPE __tmp_val__;                                              \
    string __tmp_string_val__;                                     \
    bit   __tmp_success_val__;                                     \
    `uvm_resource_read(__tmp_success_val__,                        \
                         RSRC,                                     \
                         string,                                   \
                         __tmp_string_val__,                       \
                         OBJ)                                      \
    if (__tmp_success_val__ &&                                     \
	uvm_enum_wrapper#(TYPE)::from_name(__tmp_string_val__,     \
					   __tmp_val__)) begin     \
       VAL = __tmp_val__;                                          \
       SUCCESS = __tmp_success_val__;                              \
    end                                                            \
  end                                                              \
  if (!SUCCESS) begin                                              \
     typedef bit [$bits(TYPE)-1:0] __tmp_int_t__;                  \
     __tmp_int_t__                 __tmp_int_val__;                \
     bit 			   __tmp_success_val__;            \
     `uvm_resource_int_read(__tmp_success_val__,                   \
			    RSRC,                                  \
			    __tmp_int_t__,                         \
			    __tmp_int_val__,                       \
			    OBJ)                                   \
     if (__tmp_success_val__) begin                                \
       VAL = TYPE'(__tmp_int_val__);                               \
       SUCCESS = __tmp_success_val__;                              \
     end                                                           \
  end                                                              \
end

// uvm_resource_real_read
// ---------------------
// Attempts to read a real typed resource ~RSRC~,
// starting with 'real' before checking the 
// builtin intergral types.
//
// ~SUCCESS~ shall be set to true if the resource was succesfully
// read, false otherwise.
//

`define uvm_resource_real_read(SUCCESS, RSRC, VAL, OBJ=null)       \
begin                                                              \
  `uvm_resource_read(SUCCESS, RSRC, real, VAL, OBJ)                \
  if (!SUCCESS) begin                                              \
     typedef bit [63:0] __tmp_int_t__;                             \
     __tmp_int_t__      __tmp_int_val__;                           \
     bit 	        __tmp_success_val__;                       \
     `uvm_resource_int_read(__tmp_success_val__,                   \
			    RSRC,                                  \
			    __tmp_int_t__,                         \
			    __tmp_int_val__,                       \
			    OBJ)                                   \
     if (__tmp_success_val__) begin                                \
       VAL = $bitstoreal(__tmp_int_val__);                         \
       SUCCESS = __tmp_success_val__;                              \
     end                                                           \
  end                                                              \
end

`endif //  `ifndef UVM_RESOURCE_DEFINES_SVH
