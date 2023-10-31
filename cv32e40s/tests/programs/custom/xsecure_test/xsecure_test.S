// Copyright 2023 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

.section .text


// Functions
.global setup_pmp
.global set_u_mode


setup_pmp:
	// Set pmp addr to 0xFFFF_FFFF
	li	t0, 0xFFFFFFFF
	csrrw	x0, pmpaddr0, t0

	// Set pmp region TOR and read/write/execute
	li	t0, ((1 << 3) + (7 << 0))
	csrrw	x0, pmpcfg0, t0

	// Return to caller
	jalr	x0, 0(ra)


set_u_mode: // puts the core in usermode.
	// Zero "mstatus" to set MPP=umode
	li	t0, 0x1800
	csrrc   x0, mstatus, t0 // clear the mstatus (mpp -> User mode).
	csrrw 	x0, mepc, ra
	mret
