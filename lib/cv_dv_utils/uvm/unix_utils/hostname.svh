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
//  Description : This function returns the name of the host we are running on.
//                
// 
// ----------------------------------------------------------------------------

function string hostname( );

   automatic string line = "";
   automatic string command;
   automatic int    fd;
   automatic string tmp_file = tmp_filename( .use_slash_tmp( 1 ), .prefix( "uname" ) );

   // Try using env variable
   line = getenv("HOSTNAME");
   if ( line != "" ) return line;

   // Otherwise try using system call to uname
   //
   // Make the call to uname and redirect to a file
   command = $sformatf("uname -n > %0s", tmp_file );
   $system(command);

   // Read the file
   fd= $fopen( tmp_file, "r" );
   if (fd) begin
      int ret_code;
      ret_code = $fgets( line, fd );
      $fclose(fd);
   end // if

   // Read the file
   //
   return line;

endfunction : hostname


