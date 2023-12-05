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


import param_sweeper_pkg::*;

module tb;
	Design_params DP;

	initial begin
		DP = new();
		// ARG1: 1 => exhaustive mode | 0 => corner mode
		// ARG2: 1 => Print the generated parameters value | 0 => not print (it is the default value in case not argument is passed)		
		DP.Iterate_EXHAUSTIVE_or_CORNER(0,0);
		
		// ARG1: 1 => Print the generated parameters value | 0 => not print (it is the default value in case not argument is passed)	
		//DP.RAMDOM(0); 

	end
endmodule
