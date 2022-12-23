# riscvISACOV: RISC-V SystemVerilog Functional Coverage: RV32ZCBZMUL

ISA Extension: RV32ZCBZMUL  
Specification: Zcb Code Size Reduction extension and M or Zmmul  
Version:       1.0.0  
XLEN:          32  

Instructions:  1  
Covergroups:   1  
Coverpoints total:   7  
Coverpoints Compliance Basic:  3  
Coverpoints Compliance Extended:  4  

| Extension | Subset | Instruction| Covergroup | Coverpoint     | Coverpoint Description | Coverpoint Level  |
| ----------| ------ | ---------- | ---------- | -------------- | ---------------------- | ----------------- |
| RV32ZCBZMUL           |        ZcbZmul |      c-mul |    c_mul_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             |     cp_rs2p | RS2 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended
|                       |                |            |             | cp_rs2p_toggle | RS2P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs2p_maxvals | RDP Max values | Compliance Extended


