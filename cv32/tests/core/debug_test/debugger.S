
/*
**
** Copyright 2020 OpenHW Group
** 
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
** 
**     https://solderpad.org/licenses/
** 
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
** 
*******************************************************************************
** Debugger code
*******************************************************************************
*/

.section .debugger, "ax"
.global _debugger_start
.global glb_debug_status
.global glb_hart_status
.global __debugger_stack_start
        
_debugger_start:        
        // Debugger Stack
        csrw dscratch, a0       // dscratch0
        la a0, __debugger_stack_start
        //sw t0, 0(a0)
        csrw 0x7b3, t0      	// dscratch1
        sw t1, 4(a0)
        sw t2, 8(a0)
        sw a1, 12(a0)
        sw a2, 16(a0)
        // Increment glb_debug_status
        la a1, glb_debug_status
        lw t1, 0(a1)
        addi t1,t1,1
        sw t1, 0(a1)
        // Determine Test to execute in debugger code
        la a2, glb_hart_status
        lw t2, 0(a2)
	li t0, 0
	beq t2,t0,_debugger_end // Test 0
	li t0,1
	beq t2,t0,_debugger_ebreak // Test 1
_debugger_ebreak:
	// Repeat executing debug code until debug status = 4
	li t0, 4
	beq t1,t0,_debugger_end
        csrr t0, 0x7b3
	lw t1, 4(a0)
        lw t2, 8(a0)
        lw a1, 12(a0)
        lw a2, 16(a0)
        csrr a0, dscratch
        ebreak
_debugger_end:	
        // Debugger Stack
        //lw t0, 0(a0)
        csrr t0, 0x7b3
        lw t1, 4(a0)
        lw t2, 8(a0)
        lw a1, 12(a0)
        lw a2, 16(a0)
        csrr a0, dscratch
        dret
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        nop
        
