// Copyright 2023 Silicon Laboratories Inc.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you
// may not use this file except in compliance with the License, or, at your
// option, the Apache License version 2.0.
//
// You may obtain a copy of the License at
// https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//
// See the License for the specific language governing permissions and
// limitations under the License.


enum {
  EXC_CAUSE_INSTR_ACC_FAULT       = 1,
  EXC_CAUSE_ILLEGAL_INSTR         = 2,
  EXC_CAUSE_BREAKPOINT            = 3,
  EXC_CAUSE_LOAD_ACC_FAULT        = 5,
  EXC_CAUSE_STORE_ACC_FAULT       = 7,
  EXC_CAUSE_ENV_CALL_U            = 8,
  EXC_CAUSE_ENV_CALL_M            = 11,
  EXC_CAUSE_INSTR_BUS_FAULT       = 24,
  EXC_CAUSE_INSTR_INTEGRITY_FAULT = 25,
};
