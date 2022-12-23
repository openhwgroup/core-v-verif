# riscvISACOV: RISC-V SystemVerilog Functional Coverage: RV32ZCB

ISA Extension: RV32ZCB  
Specification: Zcb Code Size Reduction extension for simple code-size saving instructions  
Version:       1.0.0  
XLEN:          32  

Instructions:  7  
Covergroups:   7  
Coverpoints total:   43  
Coverpoints Compliance Basic:  19  
Coverpoints Compliance Extended:  24  

| Extension | Subset | Instruction| Covergroup | Coverpoint     | Coverpoint Description | Coverpoint Level  |
| ----------| ------ | ---------- | ---------- | -------------- | ---------------------- | ----------------- |
| RV32ZCB               |            Zcb |      c-lbu |    c_lbu_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             |     cp_rs1p | RS1 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs1p_toggle | RS1P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended
|                       |                |            |             | cp_rs1p_maxvals | RDP Max values | Compliance Extended
| RV32ZCB               |            Zcb |      c-lhu |    c_lhu_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             |     cp_rs1p | RS1 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs1p_toggle | RS1P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended
|                       |                |            |             | cp_rs1p_maxvals | RDP Max values | Compliance Extended
| RV32ZCB               |            Zcb |       c-lh |     c_lh_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             |     cp_rs1p | RS1 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs1p_toggle | RS1P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended
|                       |                |            |             | cp_rs1p_maxvals | RDP Max values | Compliance Extended
| RV32ZCB               |            Zcb |       c-sb |     c_sb_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |     cp_rs1p | RS1 (GPR) register assignment | Compliance Basic
|                       |                |            |             |     cp_rs2p | RS2 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rs1p_toggle | RS1P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs1p_maxvals | RDP Max values | Compliance Extended
|                       |                |            |             | cp_rs2p_toggle | RS2P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs2p_maxvals | RDP Max values | Compliance Extended
| RV32ZCB               |            Zcb |       c-sh |     c_sh_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |     cp_rs1p | RS1 (GPR) register assignment | Compliance Basic
|                       |                |            |             |     cp_rs2p | RS2 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rs1p_toggle | RS1P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs1p_maxvals | RDP Max values | Compliance Extended
|                       |                |            |             | cp_rs2p_toggle | RS2P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs2p_maxvals | RDP Max values | Compliance Extended
| RV32ZCB               |            Zcb |   c-zext-b | c_zext_b_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended
| RV32ZCB               |            Zcb |      c-not |    c_not_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended


