/*
 * Copyright 2023 Dolphin Design
 * SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 */
`ifdef IMPERAS_COV

  `define IDV_INCLUDE_TRACE2COV
  `define COVER_BASE_RV32I
  `define COVER_RV32I
  `define COVER_RV32M
  `define COVER_RV32C

  `ifdef FPU
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

  `define COVER_TYPE_ASM_COUNT
  `define COVER_TYPE_ASSIGNMENTS
  `define COVER_TYPE_CSR_VALUE
  `define COVER_TYPE_FRM
  `define COVER_TYPE_SIGNS
  `define COVER_TYPE_VALUES
  // `define COVER_TYPE_ILLEGAL_INST

  // `define  COVER_TYPE_CROSS_VALUES
  `define COVER_TYPE_EQUAL
  // `define COVER_TYPE_FAULTS
  `define COVER_TYPE_MAXVALS
  `define COVER_TYPE_REG_COMPARE
  // `define COVER_TYPE_TOGGLE

  // `define COVER_TYPE_CSR
  // `define COVER_TYPE_METRIC
  `define COVER_TYPE_FPVALUES
  `define COVER_TYPE_HAZARD

`endif
