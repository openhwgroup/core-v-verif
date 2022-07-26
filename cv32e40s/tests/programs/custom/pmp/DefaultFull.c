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

void default_full()
{
  printf("\nxxxxx Checking DefaultFull xxxxxx\n");
  // initialize to 0
  uint32_t myarray[64] = {0};
  for (int i = 0; i < 64; i++)
  {
    if (myarray[i] != 0)
    {
      printf("\nInconsistant value to initializer!\n");
      printf("\nmyarray[%d] = %lx\n", i, myarray[i]);
      printf("\n");
      // exit(EXIT_FAILURE);
      exit(EXIT_FAILURE);
    }
  }

  for (int i = 0; i < 64; i++)
  {
    myarray[i] = i;

    if (myarray[i] != i)
    {
      printf("\nValues are not updated accordingly!\n");
      printf("Expected values = %d\n", i);
      printf("myarray[%d] = %lx\n", i, myarray[i]);
      printf("\n");
      exit(EXIT_FAILURE);
    }
  }
  printf("\nM-mode has the full access permissions.\n");
  printf("There's no exceptions to take care.\n");
}