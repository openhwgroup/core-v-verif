/*
 * Copyright 2023 Dolphin Design
 * SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 */

 `ifdef RV_DV_ISA_RV32IMFC
 `define RV_DV_ISA { RV32I, RV32M, RV32C, RV32F }
 `endif

 `ifdef RV_DV_ISA_RV32IMC_ZFINX
 `define RV_DV_ISA { RV32I, RV32M, RV32C, RV32ZFINX }
 `endif

 `ifdef RV_DV_ISA_RV32IMC_X
 `define RV_DV_ISA { RV32I, RV32M, RV32C, RV32X }
 `endif

 `ifdef RV_DV_ISA_RV32IMFC_X
 `define RV_DV_ISA { RV32I, RV32M, RV32C, RV32F, RV32X }
 `endif

 `ifdef RV_DV_ISA_RV32IMC_ZFINX_X
 `define RV_DV_ISA { RV32I, RV32M, RV32C, RV32ZFINX, RV32X }
 `endif
