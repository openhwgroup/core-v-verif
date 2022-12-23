# riscvISACOV: RISC-V SystemVerilog Functional Coverage: RV32ZCMT

ISA Extension: RV32ZCMT  
Specification: Zcmt Code Size Reduction extension with table jump operations  
Version:       1.0.0  
XLEN:          32  

Instructions:  2  
Covergroups:   2  
Coverpoints total:   4  
Coverpoints Compliance Basic:  4  

| Extension | Subset | Instruction| Covergroup | Coverpoint     | Coverpoint Description | Coverpoint Level  |
| ----------| ------ | ---------- | ---------- | -------------- | ---------------------- | ----------------- |
| RV32ZCMT              |           Zcmt |      cm-jt |    cm_jt_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             | cp_imm_index |   JVT index | Compliance Basic
| RV32ZCMT              |           Zcmt |    cm-jalt |  cm_jalt_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             | cp_imm_index |   JVT index | Compliance Basic


