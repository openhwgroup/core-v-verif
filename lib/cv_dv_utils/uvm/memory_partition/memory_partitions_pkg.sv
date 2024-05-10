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
//  Description : Package for the configuration of memory regions
//                
// 
// ----------------------------------------------------------------------------

package memory_partitions_pkg;

   timeunit 1ns;

   import uvm_pkg::*;

   `include "uvm_macros.svh";

   
typedef enum int { MEM_RANDOM_REGIONS = 0,  // 2 randomly chosen regions 
                   MEM_CLOSE_REGIONS  = 1,  // 2 adjacent relatively close regions 
                   MEM_EXTREME_REGIONS = 2  // Regions at the extremes of the partition 
                 } mem_region_t;

   `include "memory_partitions_cfg.svh";
endpackage : memory_partitions_pkg


