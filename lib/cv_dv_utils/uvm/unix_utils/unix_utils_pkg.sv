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
//  Description : This package includes tasks which are useful for
//                interacting with the host computer via unix.
// 
// 
// ----------------------------------------------------------------------------

package unix_utils_pkg;

   import uvm_pkg::*;
   import "DPI-C" function string getenv(input string env_name);
   import "DPI-C" function int getpid();

   `include "uvm_macros.svh";
   `include "tmp_filename.svh";
   `include "rm_file.svh";
   `include "hostname.svh";
   `include "grep.svh";
   `include "md5sum_file_check.svh";
   `include "search_replace.svh";
   `include "search_replace_file.svh";

endpackage : unix_utils_pkg
