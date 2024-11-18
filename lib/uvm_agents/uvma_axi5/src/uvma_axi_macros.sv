// Copyright 2024 CoreLab Tech
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//

`ifndef __UVMA_AXI_MACROS_SV__
  `define __UVMA_AXI_MACROS_SV__

  `define IFNDEF_DEFINE(name,value) \
    `ifndef name \
      `define name value \
  `endif

  `IFNDEF_DEFINE(UVMA_AXI_ADDR_MAX_WIDTH    , 64  )
  `IFNDEF_DEFINE(UVMA_AXI_DATA_MAX_WIDTH    , 64  )
  `IFNDEF_DEFINE(UVMA_AXI_USER_MAX_WIDTH    , 512 )
  `IFNDEF_DEFINE(UVMA_AXI_ID_MAX_WIDTH      , 64  )
  // `IFNDEF_DEFINE(UVMA_AXI_STRB_MAX_WIDTH , 8   )

  `IFNDEF_DEFINE(UVMA_AXI_MAX_NB_TXN_BURST  , 256 )
  `IFNDEF_DEFINE(UVMA_AXI_LOOP_MAX_WIDTH    , 8   )
  `IFNDEF_DEFINE(UVMA_AXI_MMUSID_MAX_WIDTH  , 32  )
  `IFNDEF_DEFINE(UVMA_AXI_MMUSSID_MAX_WIDTH , 20  )

`endif // __UVMA_AXI_MACROS_SV__
