# riscvISACOV: RISC-V SystemVerilog Functional Coverage: RV32ZCA

ISA Extension: RV32ZCA  
Specification: Zca Code Size Reduction extension for original base C Compressed instructions  
Version:       0.70.4  
XLEN:          32  

Instructions:  25  
Covergroups:   25  
Coverpoints total:   122  
Coverpoints Compliance Basic:  64  
Coverpoints Compliance Extended:  58  

| Extension | Subset | Instruction| Covergroup | Coverpoint     | Coverpoint Description | Coverpoint Level  |
| ----------| ------ | ---------- | ---------- | -------------- | ---------------------- | ----------------- |
| RV32ZCA               |          C,Zca |      c-add |    c_add_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |       cp_rd | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             |      cp_rs2 | RS2 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rs2_sign | RS2 (GPR) sign of value | Compliance Basic
|                       |                |            |             | cp_rd_toggle | RD Toggle bits | Compliance Extended
|                       |                |            |             | cp_rd_maxvals | RD Max values | Compliance Extended
|                       |                |            |             | cp_rs2_toggle | RS2 Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs2_maxvals | RD Max values | Compliance Extended
| RV32ZCA               |          C,Zca |       c-mv |     c_mv_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |       cp_rd | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             |      cp_rs2 | RS2 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rs2_sign | RS2 (GPR) sign of value | Compliance Basic
|                       |                |            |             | cp_rd_toggle | RD Toggle bits | Compliance Extended
|                       |                |            |             | cp_rd_maxvals | RD Max values | Compliance Extended
|                       |                |            |             | cp_rs2_toggle | RS2 Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs2_maxvals | RD Max values | Compliance Extended
| RV32ZCA               |          C,Zca |     c-addi |   c_addi_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |       cp_rd | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_imm_sign | Immediate value sign | Compliance Basic
|                       |                |            |             | cp_rd_toggle | RD Toggle bits | Compliance Extended
|                       |                |            |             | cp_rd_maxvals | RD Max values | Compliance Extended
| RV32ZCA               |          C,Zca | c-addi16sp | c_addi16sp_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
| RV32ZCA               |          C,Zca | c-addi4spn | c_addi4spn_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
| RV32ZCA               |          C,Zca |       c-li |     c_li_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |       cp_rd | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_imm_sign | Immediate value sign | Compliance Basic
|                       |                |            |             | cp_rd_toggle | RD Toggle bits | Compliance Extended
|                       |                |            |             | cp_rd_maxvals | RD Max values | Compliance Extended
| RV32ZCA               |          C,Zca |      c-lui |    c_lui_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |       cp_rd | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rd_toggle | RD Toggle bits | Compliance Extended
|                       |                |            |             | cp_rd_maxvals | RD Max values | Compliance Extended
| RV32ZCA               |          C,Zca |      c-and |    c_and_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             |     cp_rs2p | RS2 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended
|                       |                |            |             | cp_rs2p_toggle | RS2P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs2p_maxvals | RDP Max values | Compliance Extended
| RV32ZCA               |          C,Zca |       c-or |     c_or_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             |     cp_rs2p | RS2 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended
|                       |                |            |             | cp_rs2p_toggle | RS2P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs2p_maxvals | RDP Max values | Compliance Extended
| RV32ZCA               |          C,Zca |      c-sub |    c_sub_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             |     cp_rs2p | RS2 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended
|                       |                |            |             | cp_rs2p_toggle | RS2P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs2p_maxvals | RDP Max values | Compliance Extended
| RV32ZCA               |          C,Zca |      c-xor |    c_xor_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             |     cp_rs2p | RS2 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended
|                       |                |            |             | cp_rs2p_toggle | RS2P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs2p_maxvals | RDP Max values | Compliance Extended
| RV32ZCA               |          C,Zca |     c-andi |   c_andi_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_imm_sign | Immediate value sign | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended
| RV32ZCA               |          C,Zca |     c-beqz |   c_beqz_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |   cp_offset | Branch Immediate Offset value | Compliance Basic
|                       |                |            |             |     cp_rs1p | RS1 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rs1p_toggle | RS1P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs1p_maxvals | RDP Max values | Compliance Extended
| RV32ZCA               |          C,Zca |     c-bnez |   c_bnez_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |   cp_offset | Branch Immediate Offset value | Compliance Basic
|                       |                |            |             |     cp_rs1p | RS1 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rs1p_toggle | RS1P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs1p_maxvals | RDP Max values | Compliance Extended
| RV32ZCA               |          C,Zca |        c-j |      c_j_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |   cp_offset | Branch Immediate Offset value | Compliance Basic
| RV32ZCA               |          C,Zca |      c-jal |    c_jal_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |   cp_offset | Branch Immediate Offset value | Compliance Basic
| RV32ZCA               |          C,Zca |     c-jalr |   c_jalr_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rs1 | RS1 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rs1_sign | RS1 (GPR) sign of value | Compliance Basic
|                       |                |            |             | cp_rs1_toggle | RS1 Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs1_maxvals | RD Max values | Compliance Extended
| RV32ZCA               |          C,Zca |       c-jr |     c_jr_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rs1 | RS1 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rs1_toggle | RS1 Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs1_maxvals | RD Max values | Compliance Extended
| RV32ZCA               |          C,Zca |       c-lw |     c_lw_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             |     cp_rs1p | RS1 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs1p_toggle | RS1P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended
|                       |                |            |             | cp_rs1p_maxvals | RDP Max values | Compliance Extended
| RV32ZCA               |          C,Zca |     c-lwsp |   c_lwsp_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |       cp_rd | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rd_toggle | RD Toggle bits | Compliance Extended
|                       |                |            |             | cp_rd_maxvals | RD Max values | Compliance Extended
| RV32ZCA               |          C,Zca |     c-slli |   c_slli_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |       cp_rd | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rd_toggle | RD Toggle bits | Compliance Extended
|                       |                |            |             | cp_rd_maxvals | RD Max values | Compliance Extended
| RV32ZCA               |          C,Zca |     c-srai |   c_srai_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended
| RV32ZCA               |          C,Zca |     c-srli |   c_srli_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rdp | RD (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rdp_toggle | RDP Toggle bits | Compliance Extended
|                       |                |            |             | cp_rdp_maxvals | RDP Max values | Compliance Extended
| RV32ZCA               |          C,Zca |       c-sw |     c_sw_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |     cp_rs1p | RS1 (GPR) register assignment | Compliance Basic
|                       |                |            |             |     cp_rs2p | RS2 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rs1p_toggle | RS1P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs1p_maxvals | RDP Max values | Compliance Extended
|                       |                |            |             | cp_rs2p_toggle | RS2P Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs2p_maxvals | RDP Max values | Compliance Extended
| RV32ZCA               |          C,Zca |     c-swsp |   c_swsp_cg | cp_asm_count | Number of times instruction is executed | Compliance Basic
|                       |                |            |             |      cp_rs2 | RS2 (GPR) register assignment | Compliance Basic
|                       |                |            |             | cp_rs2_toggle | RS2 Toggle bits | Compliance Extended
|                       |                |            |             | cp_rs2_maxvals | RD Max values | Compliance Extended


