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

interface generic_if (input bit clk_i, input bit rst_ni);

    //--------------------------------------------------------------------
    // Parameters
    //--------------------------------------------------------------------
    parameter type req_t = logic;
    parameter type rsp_t = logic;


  //     request interface
  logic                  req_valid;
  logic                  req_ready;
  req_t                  req;

  //      response interface
  logic                  rsp_valid;
  logic                  rsp_ready;
  rsp_t                  rsp;
  
  // ------------------------------------------------------------------------
  // Delay Task
  // ------------------------------------------------------------------------
  task wait_n_clocks( int N );          // pragma tbx xtf
    begin
      if( N > 0) begin
        @(posedge clk_i);
        repeat (N-1) @( posedge clk_i );
      end
    end
  endtask : wait_n_clocks


endinterface
