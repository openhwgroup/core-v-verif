/*
 * Copyright 2023 Dolphin Design
 * SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 */

//Additional defines based on DUT config parameters
`ifdef PULP //PULP = 1
  `ifndef FPU //FPU = 0
    `define RV_DV_ISA { RV32I, RV32M, RV32C, RV32X }
  `else //FPU = 1
    `ifndef ZFINX
      `define RV_DV_ISA { RV32I, RV32M, RV32C, RV32X, RV32F, RV32FC }
    `else
      `define FP_IN_X_REGS
      `define RV_DV_ISA { RV32I, RV32M, RV32C, RV32X, RV32ZFINX }
    `endif
  `endif
`else //PULP = 0, FPU = 1
  `ifdef FPU
    `ifndef ZFINX
      `define RV_DV_ISA { RV32I, RV32M, RV32C, RV32F, RV32FC }
    `else
      `define FP_IN_X_REGS
      `define RV_DV_ISA { RV32I, RV32M, RV32C, RV32ZFINX }
    `endif
  `endif
`endif

//Following defines are provided to allow overwrite from test yaml files
`ifdef RV_DV_ISA_RV32IMFC
`define RV_DV_ISA { RV32I, RV32M, RV32C, RV32F, RV32FC }
`endif

`ifdef RV_DV_ISA_RV32IMC_ZFINX
`define FP_IN_X_REGS
`define RV_DV_ISA { RV32I, RV32M, RV32C, RV32ZFINX }
`endif

`ifdef RV_DV_ISA_RV32IMC_X
`define RV_DV_ISA { RV32I, RV32M, RV32C, RV32X }
`endif

`ifdef RV_DV_ISA_RV32IMFC_X
`define RV_DV_ISA { RV32I, RV32M, RV32C, RV32F, RV32FC, RV32X }
`endif

`ifdef RV_DV_ISA_RV32IMC_ZFINX_X
`define FP_IN_X_REGS
`define RV_DV_ISA { RV32I, RV32M, RV32C, RV32ZFINX, RV32X }
`endif


//Base default ISA for tests if nothing else is defined
`ifndef RV_DV_ISA
`define RV_DV_ISA { RV32I, RV32M, RV32C }
`endif
