/*
 * Copyright 2023 Dolphin Design
 * SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 */
`ifdef IMPERAS_COV
  `define IDV_INCLUDE_TRACE2COV
  `define COVER_BASE_RV32I
  `define COVER_LEVEL_COMPL_BAS
  //`define COVER_LEVEL_COMPL_EXT
  //`define COVER_LEVEL_DV_UP_BAS
  //`define COVER_LEVEL_DV_UP_EXT
  //`define COVER_LEVEL_DV_PR_BAS
  //`define COVER_LEVEL_DV_PR_EXT
  `define COVER_RV32I
  `define COVER_RV32M
  `define COVER_RV32C
  `define COVER_RVVI_METRICS

  `ifdef FPU
    `define COVER_CSR_FCSR
    `define COVER_CSR_FFLAGS
    `define COVER_CSR_FRM
    `ifndef ZFINX
      `define COVER_RV32F
      `define COVER_RV32ZCF
    `else
      `define COVER_RV32ZFINX
    `endif
  `else
    `define COVER_RV32F_ILLEGAL
    `define COVER_RV32ZCF_ILLEGAL
  `endif

  `ifdef PULP
    `define COVER_XPULPV2
    `ifdef CLUSTER
      `define COVER_XPULPV2C
    `else
      `define COVER_XPULPV2C_ILLEGAL
    `endif
  `else
    `define COVER_XPULPV2_ILLEGAL
    `define COVER_XPULPV2C_ILLEGAL
  `endif
`endif
