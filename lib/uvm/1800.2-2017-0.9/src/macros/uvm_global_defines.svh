//------------------------------------------------------------------------------
// Copyright 2014 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2015 NVIDIA Corporation
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
//------------------------------------------------------------------------------
`ifndef UVM_GLOBAL_DEFINES_SVH
`define UVM_GLOBAL_DEFINES_SVH

//
// Title -- NODOCS -- Global Macros 
//------------------------
// Group -- NODOCS -- Global object Macro definitions can be used in multiple locations
//------------------------
//
// MACRO -- NODOCS -- `UVM_MAX_STREAMBITS
//
// Defines the maximum bit vector size for integral types. 
// Used to set uvm_bitstream_t

`ifndef UVM_MAX_STREAMBITS
 // @uvm-ieee 1800.2-2017 auto 16.2.3.8
 // @uvm-ieee 1800.2-2017 auto 16.4.6.1
 // @uvm-ieee 1800.2-2017 auto 16.5.4.8
 // @uvm-ieee 1800.2-2017 auto B.6.2
 `define UVM_MAX_STREAMBITS 4096
`endif


// MACRO -- NODOCS -- `UVM_PACKER_MAX_BYTES
//
// Defines the maximum bytes to allocate for packing an object using
// the <uvm_packer>. Default is <`UVM_MAX_STREAMBITS>, in ~bytes~.

`ifndef UVM_PACKER_MAX_BYTES
 `define UVM_PACKER_MAX_BYTES `UVM_MAX_STREAMBITS
`endif

//------------------------
// Group -- NODOCS -- Global Time Macro definitions that can be used in multiple locations
//------------------------

// MACRO -- NODOCS -- `UVM_DEFAULT_TIMEOUT
//
// The default timeout for simulation, if not overridden by
// <uvm_root::set_timeout> or <uvm_cmdline_processor::+UVM_TIMEOUT>
//

`define UVM_DEFAULT_TIMEOUT 9200s

`endif //  `ifndef UVM_GLOBAL_DEFINES_SVH
