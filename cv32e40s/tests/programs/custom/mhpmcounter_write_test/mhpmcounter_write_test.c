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
    __asm__ volatile("csrrs x0, 0xB03, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB04, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB05, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB06, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB07, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB08, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB09, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB0A, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB0B, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB0C, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB0D, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB0E, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB0F, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB10, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB11, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB12, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB13, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB14, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB15, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB16, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB17, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB18, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB19, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB1A, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB1B, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB1C, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB1D, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB1E, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB1F, %0" :: "r"(reg));

    return 0;
}

int write_mhpmcounterhs()
{
    uint32_t reg = 0;
    __asm__ volatile("csrrs x0, 0xB83, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB84, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB85, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB86, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB87, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB88, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB89, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB8A, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB8B, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB8C, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB8D, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB8E, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB8F, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB90, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB91, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB92, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB93, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB94, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB95, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB96, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB97, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB98, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB99, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB9A, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB9B, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB9C, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB9D, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB9E, %0" :: "r"(reg));
    __asm__ volatile("csrrs x0, 0xB9F, %0" :: "r"(reg));

    return 0;
}

int check_mhpmcounters_are_zero()
{
    uint32_t reg = 0;
    __asm__ volatile("csrr %0, 0xB03" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB04" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB05" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB06" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB07" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB08" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB09" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB0A" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB0B" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB0C" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB0D" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB0E" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB0F" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB10" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB11" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB12" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB13" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB14" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB15" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB16" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB17" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB18" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB19" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB1A" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB1B" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB1C" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB1D" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB1E" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB1F" : "=r"(reg));
    if(reg != 0) return 1;

    return 0;
}

int check_mhpmcounterhs_are_zero()
{
    uint32_t reg = 0;
    __asm__ volatile("csrr %0, 0xB83" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB84" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB85" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB86" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB87" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB88" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB89" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB8A" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB8B" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB8C" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB8D" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB8E" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB8F" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB90" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB91" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB92" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB93" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB94" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB95" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB96" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB97" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB98" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB99" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB9A" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB9B" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB9C" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB9D" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB9E" : "=r"(reg));
    if(reg != 0) return 1;
    __asm__ volatile("csrr %0, 0xB9F" : "=r"(reg));
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
