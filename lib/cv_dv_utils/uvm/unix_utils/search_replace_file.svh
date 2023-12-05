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
//  Description : This function allows the user to open a text file,
//                perform a series of search and replace operations,
//                and then write the result into a new text file.
//
//                The function is a a bit like 
//
//                cat filename_in | sed -e 's/from/to/' > filename_out
//
//                Except that the argument convert contains an associative
//                array. The keys are the search strings (from) and the
//                contents are the replacemen strings (to).
//                
// 
// ----------------------------------------------------------------------------

function void search_replace_file( input string filename_in,
                                   input string filename_out,
                                   input string convert[string],
                                   input string options = "" );   // can pass 'g' to indicate replace all, 
                                                                      // otherwise first match

   static    string msg_prefix = "search_replace_file";
   automatic int fd_in, fd_out;
   string    line_in, line_out;
   automatic int status;

   // Open input file
   fd_in = $fopen( filename_in, "r" );
   if (!fd_in) begin
      `uvm_fatal( msg_prefix, $sformatf("Unable to open %0s for reading", filename_in ) );
   end // if

   // Open output file
   fd_out = $fopen( filename_out, "w" );
   if (!fd_out) begin
      `uvm_fatal( msg_prefix, $sformatf("Unable to open %0s for writing", filename_out ) );
   end // if

   // Scan input file
   while ( !$feof(fd_in) ) begin
      status = $fgets( line_in, fd_in );
      line_out = search_replace( line_in, convert, options );
      $fwrite( fd_out, line_out );
   end // while

   // Close the files
   $fclose(fd_in);
   $fclose(fd_out);


endfunction : search_replace_file


