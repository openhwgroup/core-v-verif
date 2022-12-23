# riscvISACOV: RISC-V SystemVerilog Functional Coverage: RV32ZCBZBB

ISA Extension: RV32ZCBZBB  
Specification: Zcb Code Size Reduction extension and Zbb Bitmanip  
Version:       1.0.0  
XLEN:          32  

Instructions:  3  
Covergroups:   3  
Coverpoints total:   12  
Coverpoints Compliance Basic:  6  
Coverpoints Compliance Extended:  6  

| Extension | Subset | Instruction| Covergroup | Coverpoint     | Coverpoint Description | Coverpoint Level  |
| ----------| ------ | ---------- | ---------- | -------------- | ---------------------- | ----------------- |
| RV32ZCBZBB            |         ZcbZbb |   c-sext-b | c_sext_b_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended
| RV32ZCBZBB            |         ZcbZbb |   c-zext-h | c_zext_h_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended
| RV32ZCBZBB            |         ZcbZbb |   c-sext-h | c_sext_h_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended


