// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`ifndef __UVMA_CLIC_TDEFS_SV__
`define __UVMA_CLIC_TDEFS_SV__

typedef enum {
   UVMA_CLIC_SEQ_ITEM_ACTION_ASSERT_UNTIL_ACK,
   UVMA_CLIC_SEQ_ITEM_ACTION_ASSERT,
   UVMA_CLIC_SEQ_ITEM_ACTION_DEASSERT
} uvma_clic_seq_item_action_enum;

typedef enum {
   UVMA_CLIC_MON_ACTION_IRQ
} uvma_clic_mon_action_enum;

`endif // __UVMA_CLIC_TDEFS_SV__
