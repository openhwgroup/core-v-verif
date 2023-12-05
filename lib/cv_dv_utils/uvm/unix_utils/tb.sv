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

import unix_utils_pkg::*;

initial begin
   md5sum_file_check( 
       '{ "test_file1":"cb93b1e9dde75591bcae130d136d4b14",
          "test_file2":"a6b7cf6cfcaa25085e277d539fc7e5e6" },
            ,
            "test_data"
      );

end

static string replace [ string ] = { "cat":"dog", "fox":"hen" };

initial begin
   static string original = "The cat chased the fox" ;

   $display( "Before:%0s" , original );
   $display( "After :%0s" , search_replace( original, replace ) );
end

initial begin
   search_replace_file( "test.txt", "out.txt", replace );
end

endmodule : tb
