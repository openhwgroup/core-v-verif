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
//  Description : This function provides a unique filename in the /tmp
//                directory that can be used for writing.
//
//                The user can optionally provide a prefix
//                
// 
// ----------------------------------------------------------------------------

function string tmp_filename( input use_slash_tmp=1, 
                              input string prefix="" );

    automatic string fname;
    automatic string tmp_dir = use_slash_tmp ? "/tmp/" : "./" ;
    automatic int    max_count = 100;
    automatic string command;

    do begin
       fname = $sformatf("%0stmp__%0s%0s%0d%0d", 
               tmp_dir, prefix, 
               (prefix =="" ? "" : "__" ),
               $urandom_range(1000,9999),
               getpid() );  // unquify with 4 digits
       max_count--;
       command = $sformatf("test -r %0s", fname ) ;
    end while ( ($system(command) == 1) && ( max_count > 0 ) );

    if ( max_count == 0 ) begin
       `uvm_fatal("Failed to find a temporary file name", 
            $sformatf("tmp_dir=%0s prefix=%0s", tmp_dir, prefix ) );
    end

    return fname;

endfunction : tmp_filename

