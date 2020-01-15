//----------------------------------------------------------------------
// Copyright 2011-2012 Paradigm Works
// Copyright 2007-2011 Mentor Graphics Corporation
// Copyright 2010-2013 Synopsys, Inc.
// Copyright 2007-2018 Cadence Design Systems, Inc.
// Copyright 2010 AMD
// Copyright 2014-2015 NVIDIA Corporation
// Copyright 2017 Cisco Systems, Inc.
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

`ifndef UVM_VERSION_DEFINES_SVH
`define UVM_VERSION_DEFINES_SVH

`define UVM_VERSION 2016


// Title --NODOCS-- UVM Version Defines

// Group --NODOCS-- UVM Version Ladder
// The following defines are provided as an indication of 
// how this implementation release relates to previous UVM 
// implementation releases from Accellera.

`ifdef UVM_ENABLE_DEPRECATED_API
// Macro --NODOCS-- UVM_POST_VERSION_1_1
// Indicates that this version of the UVM came after the
// 1.1 versions, including the various 1.1 fix revisions.  
`define UVM_POST_VERSION_1_1
`endif // UVM_ENABLE_DEPRECATED_API

`endif // UVM_VERSION_DEFINES_SVH
