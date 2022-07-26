// Copyright 2022 OpenHW Group
// Copyright 2022 Silicon Labs, Inc.
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
// SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0

#include "pmp.h"

void default_none()
{
  uint32_t mstatus;

  // int mpp = 0x1800;
  __asm__ volatile("csrrs %0, 0x300, x0\n"
                   //  "csrrs %1, 0x341, x0\n"
                   : "=r"(mstatus));
  // if in m mode change to u mode
  if (mstatus == 0x1800)
  {
    printf("\nooooo out of reset ooooo\n");
    // printf("\nmepc before mode switching = %lx\n", rtnaddr);

    change_mode();
    // asm volatile("ecall");
    __asm__ volatile("csrrs %0, 0x300, x0\n"
                     : "=r"(mstatus));
    printf("\nbbbbb back from the handler to M mode mmmmm\n");
    __asm__ volatile("csrrs %0, 0x300, x0\n"
                     : "=r"(mstatus));
    printf("\tmstatus = %lx\n", mstatus);
    printf("\nuuuu U mode test pass uuuuu\n\n");
  }
  exit(EXIT_FAILURE);
}