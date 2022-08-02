/*
**
** Copyright 2022 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
** https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
*******************************************************************************
**
** Assembly file which holds helper functions used in 'illegal_access_loop_tests.c' to declare pmp_regions or switch privilege_modes. 
**
*******************************************************************************
*/

.section .text

.global setup_pmp
.global set_u_mode

setup_pmp:
	// Set pmp addr to 0xFFFF_FFFF
	li	t0, 0xFFFFFFFF
	csrrw	x0, pmpaddr0, t0

	// Set pmp region TOR and read/write/execute
	li	t0, ((1 << 3) + (7 << 0))
	csrrw	x0, pmpcfg0, t0

	ret

set_u_mode: // puts the core in usermode.
	li	t0, 0x1800 // load as bitmask
	csrrc   x0, mstatus, t0 // clear the mstatus (mpp -> User mode).
	csrrw 	x0, mepc, ra
	mret