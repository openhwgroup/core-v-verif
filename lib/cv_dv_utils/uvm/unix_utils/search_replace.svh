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
//  Description : This function takes in a string, and a list of replacements.
//                It performs the replacements and then returns the resulting
//                string.
//                
// 
// ----------------------------------------------------------------------------

function automatic string search_replace( input string     string_in,
                                          input string     convert[string],
                                          input string     options = "" );   // can pass 'g' to indicate replace all, 
                                                                 // otherwise first match

   string from, to;


   // iterate over the replacements
   if ( convert.first( from ) ) do begin
      to = convert[from];
//      $display("Replacing %0s to %0s in %0s", from, to, string_in ) ;
      for( int i=0 ; i <= ( string_in.len() - from.len() ) ; i ++ ) begin
//         $display("i=%0d %0s", i, string_in.substr(i, i+from.len()-1 ) );
         if ( string_in.substr( i, i+from.len()-1 ) == from ) begin
//             $display("X=%0d Y=%0d S=%0s", i+from.len()-1, string_in.len()-1, string_in );
//            $display("A=%0s B=%0s C=%0s", string_in.substr( 0, i-1 ), to,  string_in.substr( i+from.len()-1, string_in.len()-1 ) );
//            $display("C=%0s", string_in.substr( 6, 21 ) );
            string_in = { string_in.substr( 0, i-1 ),
                          to,
                          string_in.substr( i+from.len(), string_in.len()-1 ) };
         end // if
      end // for

   end while ( convert.next( from ) );

   return string_in;

endfunction : search_replace


