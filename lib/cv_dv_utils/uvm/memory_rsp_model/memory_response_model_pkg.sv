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
//  Description : 
//                
// 
// ----------------------------------------------------------------------------

package memory_rsp_model_pkg;

    timeunit 1ns;

    import uvm_pkg::*;
    
    // The configuration variable rsp_order of class memory_rsp_cfg is of following type. 
    // It is used to define the order in which the responses are sent.
    typedef enum {
	    IN_ORDER_RSP, 
        OUT_OF_ORDER_RSP,
	    INVERSE_ORDER_RSP
    } memory_rsp_order_t;

    // The configuration variale rsp_mode of class memory_rsp_cfg is of following type. 
    // It is used to define the delay between each response.
    typedef enum {
	    NORMAL_RSP, 
	    ZERO_DELAY_RSP,
	    FIXED_DELAY_RSP
    } memory_rsp_mode_t;



    // The configuration variale m_bp of class memory_rsp_cfg is of following type. 
    // It is used to define the back pressure to be generated 
    typedef enum {
       NEVER,
       LIGHT, 
       MEDIUM,
       HEAVY
    } bp_t;


    // Type of memory tranasction 
    typedef enum logic [1:0] {
        MEM_WRITE    = 2'b00,
        MEM_READ     = 2'b01,
        MEM_ATOMIC   = 2'b10,
        RESERVED     = 2'b11
    } mem_command_t;



    // MRM supports following Atomic operations. 
    // It is based on the IHI0022G_b_amba_axi_protocol_specification from ARM(TM).
    typedef enum logic [3:0] {
        MEM_ATOMIC_ADD  = 4'b0000,
        MEM_ATOMIC_CLR  = 4'b0001, // NAND
        MEM_ATOMIC_SET  = 4'b0010, // OR
        MEM_ATOMIC_EOR  = 4'b0011,
        MEM_ATOMIC_SMAX = 4'b0100,
        MEM_ATOMIC_SMIN = 4'b0101,
        MEM_ATOMIC_UMAX = 4'b0110,
        MEM_ATOMIC_UMIN = 4'b0111,
        MEM_ATOMIC_SWAP = 4'b1000,
        MEM_ATOMIC_CMP  = 4'b1001,
        //  Reserved           = 4'b1010,
        //  Reserved           = 4'b1011,
        MEM_ATOMIC_LDEX = 4'b1100,
        MEM_ATOMIC_STEX = 4'b1101
        //  Reserved           = 4'b1110,
        //  Reserved           = 4'b1111
    } mem_atomic_t;



    `include "uvm_macros.svh";
    `include "memory_response_model_cfg.svh";
    `include "memory_response_model.svh";

endpackage :memory_rsp_model_pkg


