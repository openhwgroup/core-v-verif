/*
** Copyright 2022 OpenHW Group
**
** SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
** Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may not use this file except in compliance
** with the License, or, at your option, the Apache License version 2.0.  You may obtain a copy of the License at
**                                        https://solderpad.org/licenses/SHL-2.1/
** Unless required by applicable law or agreed to in writing, any work distributed under the License is distributed on
** an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.  See the License for the
** specific language governing permissions and limitations under the License.
*******************************************************************************
**
** Assembly functions to help the tests in the zc_tests.c source file.
**
*******************************************************************************
*/

// _GEN END OF HEADER GEN_

// Funtions
enable_all_irq:
  //set all fields of mie, hardwired are ignored (WARL)
  li	t0, 0xFFFFFFFF
	 csrrw x0, mie, t0

  li	t0, 0x00000008
	 csrrs x0, mstatus, t0

  jalr	x0, 0(ra)

trigger_irq:
  // trigger irq
  li  t0, 0x00800140
  la  t1, glb_irq_line
  lw  t2, 0(t1)
  la  t1, glb_irq_delay
  lw  t3, 0(t1)
  sw  t2, 0(t0)
  sw  t3, 4(t0)

  //return to caller
  jalr	x0, 0(ra)

