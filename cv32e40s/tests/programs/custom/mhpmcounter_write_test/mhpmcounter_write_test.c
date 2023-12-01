// Copyright 2023 Silicon Labs, Inc.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0.
//
// You may obtain a copy of the License at
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>


int write_mhpmcounters()
{
    uint32_t reg = 0;
    __asm__ volatile("mv %0, x0" : "=r"(reg));
    __asm__ volatile("not %0, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter3, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter4, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter5, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter6, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter7, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter8, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter9, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter10, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter11, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter12, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter13, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter14, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter15, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter16, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter17, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter18, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter19, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter20, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter21, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter22, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter23, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter24, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter25, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter26, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter27, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter28, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter29, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter30, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter31, %0" :: "r"(reg));

    return 0;
}

int write_mhpmcounterhs()
{
    uint32_t reg = 0;
    __asm__ volatile("mv %0, x0" : "=r"(reg));
    __asm__ volatile("not %0, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter3h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter4h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter5h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter6h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter7h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter8h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter9h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter10h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter11h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter12h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter13h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter14h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter15h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter16h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter17h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter18h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter19h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter20h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter21h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter22h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter23h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter24h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter25h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter26h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter27h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter28h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter29h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter30h, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, mhpmcounter31h, %0" :: "r"(reg));

    return 0;
}

int check_mhpmcounters_are_zero()
{
    uint32_t reg = 0;
    __asm__ volatile("csrr %0, mhpmcounter3" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter4" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter5" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter6" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter7" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter8" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter9" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter10" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter11" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter12" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter13" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter14" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter15" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter16" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter17" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter18" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter19" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter20" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter21" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter22" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter23" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter24" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter25" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter26" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter27" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter28" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter29" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter30" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter31" : "=r"(reg));
    if(reg != 0) return 1;

    return 0;
}

int check_mhpmcounterhs_are_zero()
{
    uint32_t reg = 0;
    __asm__ volatile("csrr %0, mhpmcounter3h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter4h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter5h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter6h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter7h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter8h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter9h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter10h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter11h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter12h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter13h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter14h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter15h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter16h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter17h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter18h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter19h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter20h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter21h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter22h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter23h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter24h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter25h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter26h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter27h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter28h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter29h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter30h" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, mhpmcounter31h" : "=r"(reg));
    if(reg != 0) return 1;

    return 0;
}


int main()
{
    uint32_t is_failure = 0;

    write_mhpmcounters();
    write_mhpmcounterhs();

    is_failure += check_mhpmcounters_are_zero();
    is_failure += check_mhpmcounterhs_are_zero();

    if (is_failure) return EXIT_FAILURE;
    return EXIT_SUCCESS;

}
