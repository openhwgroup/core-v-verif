# ISA module

## RV32I Register-Immediate Instructions feature

### 000_ADDI sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** addi rd, rs1, imm[11:0]
rd = rs1 + Sext(imm[11:0])
Arithmetic overflow is lost and ignored
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** addi rd, rs1, imm[11:0]
rd = rs1 + Sext(imm[11:0])
Arithmetic overflow is lost and ignored
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
immi value is +ve, -ve and zero
All combinations of rs1 and immi +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of immi are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P000_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** addi rd, rs1, imm[11:0]
rd = rs1 + Sext(imm[11:0])
Arithmetic overflow is lost and ignored
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P000_I002
* **Comments:** 

### 001_XORI sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** xori rd, rs1, imm[11:0]
rd = rs1 ^ Sext(imm[11:0])
Note: this is a bitwise, not logical operation
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P001_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** xori rd, rs1, imm[11:0]
rd = rs1 ^ Sext(imm[11:0])
Note: this is a bitwise, not logical operation
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
immi value is +ve, -ve and zero
All combinations of rs1 and immi +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of immi are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P001_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** xori rd, rs1, imm[11:0]
rd = rs1 ^ Sext(imm[11:0])
Note: this is a bitwise, not logical operation
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P001_I002
* **Comments:** 

### 002_ORI sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** ori rd, rs1, imm[11:0]
rd = rs1 | Sext(imm[11:0])
Note: this is a bitwise, not logical operation
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P002_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** ori rd, rs1, imm[11:0]
rd = rs1 | Sext(imm[11:0])
Note: this is a bitwise, not logical operation
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
immi value is +ve, -ve and zero
All combinations of rs1 and immi +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of immi are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P002_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** ori rd, rs1, imm[11:0]
rd = rs1 | Sext(imm[11:0])
Note: this is a bitwise, not logical operation
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P002_I002
* **Comments:** 

### 003_ANDI sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** andi rd, rs1, imm[11:0]
rd = rs1 &  Sext(imm[11:0])
Note: this is a bitwise, not logical operation
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P003_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** andi rd, rs1, imm[11:0]
rd = rs1 &  Sext(imm[11:0])
Note: this is a bitwise, not logical operation
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
immi value is +ve, -ve and zero
All combinations of rs1 and immi +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of immi are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P003_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** andi rd, rs1, imm[11:0]
rd = rs1 &  Sext(imm[11:0])
Note: this is a bitwise, not logical operation
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P003_I002
* **Comments:** 

### 004_SLTI sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** slti rd, rs1, imm[11:0]
rd = (rs1 < Sext(imm[11:0]) ? 1 : 0
Both imm and rs1 treated as signed numbers
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P004_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** slti rd, rs1, imm[11:0]
rd = (rs1 < Sext(imm[11:0]) ? 1 : 0
Both imm and rs1 treated as signed numbers
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
immi value is +ve, -ve and zero
All combinations of rs1 and immi +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of immi are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P004_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** slti rd, rs1, imm[11:0]
rd = (rs1 < Sext(imm[11:0]) ? 1 : 0
Both imm and rs1 treated as signed numbers
* **Verification goals:** Output result:

rd value is in [0,1]
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P004_I002
* **Comments:** 

### 005_SLTIU sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** sltiu rd, rs1, imm[11:0]
rd = (rs1 < Sext(imm[11:0]) ? 1 : 0
Both imm and rs1 treated as unsigned numbers
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P005_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** sltiu rd, rs1, imm[11:0]
rd = (rs1 < Sext(imm[11:0]) ? 1 : 0
Both imm and rs1 treated as unsigned numbers
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
immi value is +ve, -ve and zero
All combinations of rs1 and immi +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of immi are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P005_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** sltiu rd, rs1, imm[11:0]
rd = (rs1 < Sext(imm[11:0]) ? 1 : 0
Both imm and rs1 treated as unsigned numbers
* **Verification goals:** Output result:

rd value is in [0,1]
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P005_I002
* **Comments:** 

### 006_SLLI sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** slli rd, rs, imm[4:0]
rd = rs << imm[4:0]
Zeros are shirfted into lower bits
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P006_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** slli rd, rs, imm[4:0]
rd = rs << imm[4:0]
Zeros are shirfted into lower bits
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
immediate shamt value is [0,31]
All combinations of rs1 and immi +ve, -ve, and zero values are used
All bits of rs1 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P006_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** slli rd, rs, imm[4:0]
rd = rs << imm[4:0]
Zeros are shirfted into lower bits
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P006_I002
* **Comments:** 

### 007_SRLI sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** srli rd, rs, imm[4:0]
rd = rs >> imm[4:0]
Zeros are shirfted into upper bits
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P007_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** srli rd, rs, imm[4:0]
rd = rs >> imm[4:0]
Zeros are shirfted into upper bits
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
immediate shamt value is [0,31]
All combinations of rs1 and immi +ve, -ve, and zero values are used
All bits of rs1 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P007_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** srli rd, rs, imm[4:0]
rd = rs >> imm[4:0]
Zeros are shirfted into upper bits
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P007_I002
* **Comments:** 

### 008_SRAI sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** srli rd, rs, imm[4:0]
rd = rs >> imm[4:0]
The original sign bit is copied into the vacated upper bits
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P008_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** srli rd, rs, imm[4:0]
rd = rs >> imm[4:0]
The original sign bit is copied into the vacated upper bits
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
immediate shamt value is [0,31]
All combinations of rs1 and immi +ve, -ve, and zero values are used
All bits of rs1 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P008_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** srli rd, rs, imm[4:0]
rd = rs >> imm[4:0]
Zeros are shirfted into upper bits
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P008_I002
* **Comments:** 

### 009_LUI sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** lui rd, imm[19:0]
rd = imm[19:0] << 12
rd[11:0] is zero-filled.
* **Verification goals:** Register operands:

All possible rd registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P009_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** lui rd, imm[19:0]
rd = imm[19:0] << 12
rd[11:0] is zero-filled.
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
immediate value is zero and non-zero
All bits of immu are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P009_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** lui rd, imm[19:0]
rd = imm[19:0] << 12
rd[11:0] is zero-filled.
* **Verification goals:** Output result:

rd value is zero and non-zero
All bits of rd[31:12] are toggled (11:0 are deposited with 0)
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P009_I002
* **Comments:** 

### 010_AUIPC sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** auipc rd, imm[19:0]
rd = pc + (imm[19:0] << 12)
pc is address of auipc instruction

Assumption: arithmetic overflow is lost and ignored.
* **Verification goals:** Register operands:

All possible rd registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P010_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** auipc rd, imm[19:0]
rd = pc + (imm[19:0] << 12)
pc is address of auipc instruction

Assumption: arithmetic overflow is lost and ignored.
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
immediate value is zero and non-zero
All bits of immu are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P010_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** auipc rd, imm[19:0]
rd = pc + (imm[19:0] << 12)
pc is address of auipc instruction

Assumption: arithmetic overflow is lost and ignored.
* **Verification goals:** Output result:

rd value is zero and non-zero
All bits of rd[31:12] are toggled (11:0 are deposited with 0)
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP011_P010_I002
* **Comments:** 

## RV32I Register-Register Instructions feature

### 000_ADD sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** add rd, rs1, rs2
rd = rs1 + rs2
Arithmetic overflow is lost and ignored
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** add rd, rs1, rs2
rd = rs1 + rs2
Arithmetic overflow is lost and ignored
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
rs2 value is +ve, -ve and zero
All combinations of rs1 and rs2 +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P000_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** add rd, rs1, rs2
rd = rs1 + rs2
Arithmetic overflow is lost and ignored
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P000_I002
* **Comments:** 

### 001_SUB sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** sub rd, rs1, rs2
rd = rs1 - rs2
Arithmetic underflow is ignored
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P001_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** sub rd, rs1, rs2
rd = rs1 - rs2
Arithmetic underflow is ignored
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
rs2 value is +ve, -ve and zero
All combinations of rs1 and rs2 +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P001_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** sub rd, rs1, rs2
rd = rs1 - rs2
Arithmetic underflow is ignored
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P001_I002
* **Comments:** 

### 002_AND sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** and rd, rs1, rs2
rd = rs1 & rs2
Note: this is a bitwise, not logical operation
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P002_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** and rd, rs1, rs2
rd = rs1 & rs2
Note: this is a bitwise, not logical operation
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
rs2 value is +ve, -ve and zero
All combinations of rs1 and rs2 +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P002_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** and rd, rs1, rs2
rd = rs1 & rs2
Note: this is a bitwise, not logical operation
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P002_I002
* **Comments:** 

### 003_OR sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** or rd, rs1, rs2
rd = rs1 | rs2
Note: this is a bitwise, not logical operation
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P003_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** or rd, rs1, rs2
rd = rs1 | rs2
Note: this is a bitwise, not logical operation
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
rs2 value is +ve, -ve and zero
All combinations of rs1 and rs2 +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P003_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** or rd, rs1, rs2
rd = rs1 | rs2
Note: this is a bitwise, not logical operation
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P003_I002
* **Comments:** 

### 004_XOR sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** xor rd, rs1, rs2
rd = rs1 ^ rs2
Note: this is a bitwise, not logical operation
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P004_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** xor rd, rs1, rs2
rd = rs1 ^ rs2
Note: this is a bitwise, not logical operation
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
rs2 value is +ve, -ve and zero
All combinations of rs1 and rs2 +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P004_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** xor rd, rs1, rs2
rd = rs1 ^ rs2
Note: this is a bitwise, not logical operation
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P004_I002
* **Comments:** 

### 005_SLT sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** slt rd, rs1, rs2
rd = (rs1 < rs2) ? 1 : 0
Both rs1 ad rs2 treated as signed numbers
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P005_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** slt rd, rs1, rs2
rd = (rs1 < rs2) ? 1 : 0
Both rs1 ad rs2 treated as signed numbers
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
rs2 value is +ve, -ve and zero
All combinations of rs1 and rs2 +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P005_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** slt rd, rs1, rs2
rd = (rs1 < rs2) ? 1 : 0
Both rs1 ad rs2 treated as signed numbers
* **Verification goals:** Output result:

rd value is [0,1]
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P005_I002
* **Comments:** 

### 006_SLTU sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** sltu rd, rs1, imm[11:0]
rd = (rs1 < rs2) ? 1 : 0
Both rs1 and rs2 treated as unsigned numbers
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P006_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** sltu rd, rs1, imm[11:0]
rd = (rs1 < rs2) ? 1 : 0
Both rs1 and rs2 treated as unsigned numbers
* **Verification goals:** Input operands:

rs1 value is non-zero and zero
rs2 value is non-zero and zero
All combinations of rs1 and rs2 non-zero and zero values are used
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P006_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** sltu rd, rs1, imm[11:0]
rd = (rs1 < rs2) ? 1 : 0
Both rs1 and rs2 treated as unsigned numbers
* **Verification goals:** Output result:

rd value is [0,1]
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P006_I002
* **Comments:** 

### 007_SLL sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** sll rd, rs1, rs2
rd = rs1 << rs2[4:0]
Zeros are shirfted into lower bits
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P007_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** sll rd, rs1, rs2
rd = rs1 << rs2[4:0]
Zeros are shirfted into lower bits
* **Verification goals:** Input operands:

rs1 value is non-zero and zero
rs2 value is tested from [0,31]
All combinations of rs1 and rs2 non-zero and zero values with all shift values are used
All bits of rs1 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P007_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** sll rd, rs1, rs2
rd = rs1 << rs2[4:0]
Zeros are shirfted into lower bits
* **Verification goals:** Output result:

rd value is non-zero and zero.
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P007_I002
* **Comments:** 

### 008_SRL sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** srl rd, rs1, rs2
rd = rs1 >> rs2[4:0]
Zeros are shirfted into upper bits
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P008_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** srl rd, rs1, rs2
rd = rs1 >> rs2[4:0]
Zeros are shirfted into upper bits
* **Verification goals:** Input operands:

rs1 value is non-zero and zero
rs2 value is tested from [0,31]
All combinations of rs1 and rs2 non-zero and zero values with all shift values are used
All bits of rs1 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P008_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** srl rd, rs1, rs2
rd = rs1 >> rs2[4:0]
Zeros are shirfted into upper bits
* **Verification goals:** Output result:

rd value is non-zero and zero.
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P008_I002
* **Comments:** 

### 009_SRA sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** sra rd, rs1, rs2
rd = rs1 >> rs2[4:0]
The original sign bit is copied into the vacated upper bits
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P009_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** sra rd, rs1, rs2
rd = rs1 >> rs2[4:0]
The original sign bit is copied into the vacated upper bits
* **Verification goals:** Input operands:

rs1 value is +ve, -ve, and zero
rs2 value is tested from [0,31]
All combinations of rs1 and rs2 +ve, -ve and zero values with all shift values are used
All bits of rs1 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P009_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.4
* **Feature Description:** sra rd, rs1, rs2
rd = rs1 >> rs2[4:0]
Zeros are shirfted into upper bits
* **Verification goals:** Output result:

rd value is +ve, -ve, and zero.
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP001_P009_I002
* **Comments:** 

## RV32I Control Transfer Instructions feature

### 000_JAL sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** jal rd, imm[20:1]
rd = pc+4; pc += Sext({imm[20:1], 1’b0})
pc is calculated using signed arithmetic

jal x0, imm[20:1] (special case: unconditional jump)
pc += Sext({imm[20:1], 1’b0})
* **Verification goals:** Register operands:

All possible rd registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** jal rd, imm[20:1]
rd = pc+4; pc += Sext({imm[20:1], 1’b0})
pc is calculated using signed arithmetic

jal x0, imm[20:1] (special case: unconditional jump)
pc += Sext({imm[20:1], 1’b0})
* **Verification goals:** Input operands:

immj value is +ve, -ve, and zero
All bits of immj are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P000_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** jal rd, imm[20:1]
rd = pc+4; pc += Sext({imm[20:1], 1’b0})
pc is calculated using signed arithmetic

jal x0, imm[20:1] (special case: unconditional jump)
pc += Sext({imm[20:1], 1’b0})
* **Verification goals:** Output result:

All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P000_I002
* **Comments:** 

### 001_JALR sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** jalr rd, rs1, imm[11:0]
rd = pc+4; pc = rs1 + Sext(imm[11:0])
pc is calculated using signed arithmetic
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P001_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** jalr rd, rs1, imm[11:0]
rd = pc+4; pc = rs1 + Sext(imm[11:0])
pc is calculated using signed arithmetic
* **Verification goals:** Input operands:

immi value is +ve, -ve, and zero
All bits of immi are toggled
All bits of rs1 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P001_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** jalr rd, rs1, imm[11:0]
rd = pc+4; pc = rs1 + Sext(imm[11:0])
pc is calculated using signed arithmetic
* **Verification goals:** Output result:

All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P001_I002
* **Comments:** 

### 002_BEQ sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** beq rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1==rs2) else pc += 4
pc is calculated using signed arithmetic
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P002_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** beq rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1==rs2) else pc += 4
pc is calculated using signed arithmetic
* **Verification goals:** Input operands:

immb value is +ve, -ve, and zero
All bits of immb are toggled
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P002_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** beq rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1==rs2) else pc += 4
pc is calculated using signed arithmetic
* **Verification goals:** Output result:

Branch taken or not-taken
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P002_I002
* **Comments:** 

### 003_BNE sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** bne rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1!=rs2) else pc += 4
pc is calculated using signed arithmetic
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P003_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** bne rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1!=rs2) else pc += 4
pc is calculated using signed arithmetic
* **Verification goals:** Input operands:

immb value is +ve, -ve, and zero
All bits of immb are toggled
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P003_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** bne rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1!=rs2) else pc += 4
pc is calculated using signed arithmetic
* **Verification goals:** Output result:

Branch taken or not-taken
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P003_I002
* **Comments:** 

### 004_BLT sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** blt rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1 < rs2) else pc += 4
pc is calculated using signed arithmetic
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P004_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** blt rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1 < rs2) else pc += 4
pc is calculated using signed arithmetic
* **Verification goals:** Input operands:

immb value is +ve, -ve, and zero
All bits of immb are toggled
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P004_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** blt rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1 < rs2) else pc += 4
pc is calculated using signed arithmetic
* **Verification goals:** Output result:

Branch taken or not-taken
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P004_I002
* **Comments:** 

### 005_BGE sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** bge rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1 >= rs2) else pc += 4
pc is calculated using signed arithmetic
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P005_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** bge rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1 >= rs2) else pc += 4
pc is calculated using signed arithmetic
* **Verification goals:** Input operands:

immb value is +ve, -ve, and zero
All bits of immb are toggled
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P005_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** bge rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1 >= rs2) else pc += 4
pc is calculated using signed arithmetic
* **Verification goals:** Output result:

Branch taken or not-taken
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P005_I002
* **Comments:** 

### 006_BLTU sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** bltu rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1 < rs2) else pc += 4
pc is calculated using unsigned arithmetic
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P006_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** bltu rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1 < rs2) else pc += 4
pc is calculated using unsigned arithmetic
* **Verification goals:** Input operands:

immb value is +ve, -ve, and zero
All bits of immb are toggled
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P006_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** bltu rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1 < rs2) else pc += 4
pc is calculated using unsigned arithmetic
* **Verification goals:** Output result:

Branch taken or not-taken
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P006_I002
* **Comments:** 

### 007_BGEU sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** bgeu rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1 >= rs2) else pc += 4
pc is calculated using unsigned arithmetic
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P007_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** bgeu rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1 >= rs2) else pc += 4
pc is calculated using unsigned arithmetic
* **Verification goals:** Input operands:

immb value is +ve, -ve, and zero
All bits of immb are toggled
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P007_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.5
* **Feature Description:** bgeu rs1, rs2, imm[12:1]
pc += Sext({imm[12:1], 1’b0}) if (rs1 >= rs2) else pc += 4
pc is calculated using unsigned arithmetic
* **Verification goals:** Output result:

Branch taken or not-taken
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP002_P007_I002
* **Comments:** 

## RV32I Load and Store Instructions feature

### 000_LB sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** lb rd, rs1, imm
rd = Sext(M[rs1+imm][0:7])
rd is calculated using signed arithmetic
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** lb rd, rs1, imm
rd = Sext(M[rs1+imm][0:7])
rd is calculated using signed arithmetic
* **Verification goals:** Input operands:

immi value is +ve, -ve and zero
All combinations of rs1 and immi +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of immi are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P000_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** lb rd, rs1, imm
rd = Sext(M[rs1+imm][0:7])
rd is calculated using signed arithmetic
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P000_I002
* **Comments:** 

### 001_LH sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** lh rd, rs1, imm
rd = Sext(M[rs1+imm][0:15])
rd is calculated using signed arithmetic
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P001_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** lh rd, rs1, imm
rd = Sext(M[rs1+imm][0:15])
rd is calculated using signed arithmetic
* **Verification goals:** Input operands:

immi value is +ve, -ve and zero
All combinations of rs1 and immi +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of immi are toggled
Unaligned and aligned accesses from memory
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P001_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** lh rd, rs1, imm
rd = Sext(M[rs1+imm][0:15])
rd is calculated using signed arithmetic
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P001_I002
* **Comments:** 

### 002_LW sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** lw rd, rs1, imm
rd = Sext(M[rs1+imm][0:31])
rd is calculated using signed arithmetic
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P002_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** lw rd, rs1, imm
rd = Sext(M[rs1+imm][0:31])
rd is calculated using signed arithmetic
* **Verification goals:** Input operands:

immi value is +ve, -ve and zero
All combinations of rs1 and immi +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of immi are toggled
Unaligned and aligned accesses from memory
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P002_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** lw rd, rs1, imm
rd = Sext(M[rs1+imm][0:31])
rd is calculated using signed arithmetic
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P002_I002
* **Comments:** 

### 003_LBU sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** lbu rd, rs1, imm
rd = Zext(M[rs1+imm][0:7])
rd is calculated using unsigned arithmetic
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P003_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** lbu rd, rs1, imm
rd = Zext(M[rs1+imm][0:7])
rd is calculated using unsigned arithmetic
* **Verification goals:** Input operands:

immi value is +ve, -ve and zero
All combinations of rs1 and immi +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of immi are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P003_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** lbu rd, rs1, imm
rd = Zext(M[rs1+imm][0:7])
rd is calculated using unsigned arithmetic
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd[7:0] are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P003_I002
* **Comments:** 

### 004_LHU sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** lhu rd, rs1, imm
rd = Zext(M[rs1+imm][0:15])
rd is calculated using unsigned arithmetic
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P004_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** lhu rd, rs1, imm
rd = Zext(M[rs1+imm][0:15])
rd is calculated using unsigned arithmetic
* **Verification goals:** Input operands:

immi value is +ve, -ve and zero
All combinations of rs1 and immi +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of immi are toggled
Unaligned and aligned accesses from memory
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P004_I001
* **Comments:** 

#### 002 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** lhu rd, rs1, imm
rd = Zext(M[rs1+imm][0:15])
rd is calculated using unsigned arithmetic
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd[15:0] are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P004_I002
* **Comments:** 

### 005_SB sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** sb rs1, rs2, imm
M[rs1+imm][0:7] = rs2[0:7]
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P005_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** sb rs1, rs2, imm
M[rs1+imm][0:7] = rs2[0:7]
* **Verification goals:** Input operands:

imms value is +ve, -ve and zero
All bits of rs1 are toggled
All bits of rs2 are toggled
All bits of imms are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P005_I001
* **Comments:** 

### 006_SH sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** sh rs1, rs2, imm
M[rs1+imm][0:15] = rs2[0:15]
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P006_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** sh rs1, rs2, imm
M[rs1+imm][0:15] = rs2[0:15]
* **Verification goals:** Input operands:

imms value is +ve, -ve and zero
All bits of rs1 are toggled
All bits of rs2 are toggled
All bits of imms are toggled
Unaligned and aligned accesses to memory
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P006_I001
* **Comments:** 

### 007_SW sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** sw rs1, rs2, imm
M[rs1+imm][0:31] = rs2[0:31]
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P007_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.6
* **Feature Description:** sw rs1, rs2, imm
M[rs1+imm][0:31] = rs2[0:31]
* **Verification goals:** Input operands:

imms value is +ve, -ve and zero
All bits of rs1 are toggled
All bits of rs2 are toggled
All bits of imms are toggled
Unaligned and aligned accesses to memory
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP003_P007_I001
* **Comments:** 

## RV32I Memory Ordering Instructions feature

### 000_FENCE sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.7
* **Feature Description:** Fence operation executed
Implementation is microarchitecture specific
* **Verification goals:** Instruction executed
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP004_P000_I000
* **Comments:** 

## RV32I Environment Call and Breakpoints feature

### 000_ECALL sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.8
* **Feature Description:** Software exception vector entered
* **Verification goals:** Instruction executed
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA
Chapter 2.8
* **Feature Description:** Return control to a debugger
* **Verification goals:** Instruction executed
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P000_I001
* **Comments:** 

### 001_EBREAK sub-feature

#### 000 item

* **Requirement location:** ISA
Chapter 2.8
* **Feature Description:** Return control to a debugger
* **Verification goals:** Instruction executed
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P001_I000
* **Comments:** 

## RV32M Multiplication Operations feature

### 000_MUL sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 7.1
* **Feature Description:** mul rd, rs1, rs2
x[rd] = x[rs1] * x[rs2]
Arithmetic overflow is ignored.
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP000_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 7.1
* **Feature Description:** mul rd, rs1, rs2
x[rd] = x[rs1] * x[rs2]
Arithmetic overflow is ignored.
* **Verification goals:** Input operands:

rs1 value is non-zero and zero
rs2 value is non-zero and zero
All combinations of rs1 and rs2 non-zero and zero values are used
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP000_P000_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 7.1
* **Feature Description:** mul rd, rs1, rs2
x[rd] = x[rs1] * x[rs2]
Arithmetic overflow is ignored.
* **Verification goals:** Output result:

rd value is non-zero and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP000_P000_I002
* **Comments:** 

### 001_MULH sub-feature

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 7.1
* **Feature Description:** mulh rd, rs1, rs2
x[rd] = (x[rs1] * x[rs2]) >>s XLEN
Both rs1 and rs2 treated as signed numbers
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP000_P001_I002
* **Comments:** 

### 002_MULHU sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 7.1
* **Feature Description:** mulhu rd, rs1, rs2
x[rd] = (x[rs1] * x[rs2]) >> XLEN
Both rs1 and rs2 treated as unsigned numbers
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP000_P002_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 7.1
* **Feature Description:** mulhu rd, rs1, rs2
x[rd] = (x[rs1] * x[rs2]) >> XLEN
Both rs1 and rs2 treated as unsigned numbers
* **Verification goals:** Input operands:

rs1 value is non-zero and zero
rs2 value is non-zero and zero
All combinations of rs1 and rs2 non-zero and zero values are used
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP000_P002_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 7.1
* **Feature Description:** mulhu rd, rs1, rs2
x[rd] = (x[rs1] * x[rs2]) >> XLEN
Both rs1 and rs2 treated as unsigned numbers
* **Verification goals:** Output result:

rd value is non-zero and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP000_P002_I002
* **Comments:** 

### 003_MULHSU sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 7.1
* **Feature Description:** mulhsu rd, rs1, rs2
x[rd] = (x[rs1] * x[rs2]) >>s XLEN
rs1 treated as signed number, rs2 treated as unsigned number
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP000_P003_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 7.1
* **Feature Description:** mulhsu rd, rs1, rs2
x[rd] = (x[rs1] * x[rs2]) >>s XLEN
rs1 treated as signed number, rs2 treated as unsigned number
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
rs2 value is non-zero and zero
All combinations of rs1 and rs2 +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP000_P003_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 7.1
* **Feature Description:** mulhsu rd, rs1, rs2
x[rd] = (x[rs1] * x[rs2]) >>s XLEN
rs1 treated as signed number, rs2 treated as unsigned number
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP000_P003_I002
* **Comments:** 

## RV32M Division Operations feature

### 000_DIV sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** div rd, rs1, rs2
x[rd] = x[rs1] / x[rs2]
rd is calculated using signed arithmetic; rounding towards zero
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** div rd, rs1, rs2
x[rd] = x[rs1] / x[rs2]
rd is calculated using signed arithmetic; rounding towards zero
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
rs2 value is +ve, -ve and zero
All combinations of rs1 and rs2 +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P000_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** div rd, rs1, rs2
x[rd] = x[rs1] / x[rs2]
rd is calculated using signed arithmetic; rounding towards zero
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P000_I002
* **Comments:** 

#### 003 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** div rd, rs1, rs2
x[rd] = x[rs1] / x[rs2]
rd is calculated using signed arithmetic; rounding towards zero
* **Verification goals:** Exercise arithmetic overflow (rs1 = -2^31; rs2 = -1; returns rd = -2^31).
Exercise division by zero (returns -1 ; all bits set)
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P000_I003
* **Comments:** 

### 001_REM sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** rem rd, rs1, rs2
x[rd] = x[rs1] % x[rs2]
rd is calculated using signed arithmetic; remainder from the same division than DIV (the sign of rd equals the sign of rs1)
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P001_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** rem rd, rs1, rs2
x[rd] = x[rs1] % x[rs2]
rd is calculated using signed arithmetic; remainder from the same division than DIV (the sign of rd equals the sign of rs1)
* **Verification goals:** Input operands:

rs1 value is +ve, -ve and zero
rs2 value is +ve, -ve and zero
All combinations of rs1 and rs2 +ve, -ve, and zero values are used
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P001_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** rem rd, rs1, rs2
x[rd] = x[rs1] % x[rs2]
rd is calculated using signed arithmetic; remainder from the same division than DIV (the sign of rd equals the sign of rs1)
* **Verification goals:** Output result:

rd value is +ve, -ve and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P001_I002
* **Comments:** 

#### 003 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** rem rd, rs1, rs2
x[rd] = x[rs1] % x[rs2]
rd is calculated using signed arithmetic; remainder from the same division than DIV (the sign of rd equals the sign of rs1)
* **Verification goals:** Exercise arithmetic overflow (rs1 = -2^31; rs2 = -1; returns rd = 0).
Exercise division by zero (returns rs1)
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P001_I003
* **Comments:** 

### 002_DIVU sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** divu rd, rs1, rs2
x[rd] = x[rs1] u/ x[rs2]
rd is calculated using unsigned arithmetic; rounding towards zero
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P002_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** divu rd, rs1, rs2
x[rd] = x[rs1] u/ x[rs2]
rd is calculated using unsigned arithmetic; rounding towards zero
* **Verification goals:** Input operands:

rs1 value is non-zero and zero
rs2 value is non-zero and zero
All combinations of rs1 and rs2 non-zero and zero values are used
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P002_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** divu rd, rs1, rs2
x[rd] = x[rs1] u/ x[rs2]
rd is calculated using unsigned arithmetic; rounding towards zero
* **Verification goals:** Output result:

rd value is non-zero and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P002_I002
* **Comments:** 

#### 003 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** divu rd, rs1, rs2
x[rd] = x[rs1] u/ x[rs2]
rd is calculated using unsigned arithmetic; rounding towards zero
* **Verification goals:** Exercise division by zero (returns 2^32-1 ; all bits set)
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P002_I003
* **Comments:** 

### 003_REMU sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** remu rd, rs1, rs2
x[rd] = x[rs1] % x[rs2]
rd is calculated using unsigned arithmetic; remainder from the same division than DIVU
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P003_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** remu rd, rs1, rs2
x[rd] = x[rs1] % x[rs2]
rd is calculated using unsigned arithmetic; remainder from the same division than DIVU
* **Verification goals:** Input operands:

rs1 value is non-zero and zero
rs2 value is non-zero and zero
All combinations of rs1 and rs2 non-zero and zero values are used
All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P003_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** remu rd, rs1, rs2
x[rd] = x[rs1] % x[rs2]
rd is calculated using unsigned arithmetic; remainder from the same division than DIVU
* **Verification goals:** Output result:

rd value is non-zero and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P003_I002
* **Comments:** 

#### 003 item

* **Requirement location:** Unprivileged ISA
Chapter 7.2
* **Feature Description:** remu rd, rs1, rs2
x[rd] = x[rs1] % x[rs2]
rd is calculated using unsigned arithmetic; remainder from the same division than DIVU
* **Verification goals:** Exercise division by zero (returns rs1)
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P003_I003
* **Comments:** 

## RV32A Load-Reserved/Store-Conditional Instructions feature

### 000_LR.W sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 8.2
* **Feature Description:** lr.w rd, (rs1)
rd = [rs1]
A load occurs to address at rs1 with the results loaded to rd.
Misaligned address should cause an exception
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 8.2
* **Feature Description:** lr.w rd, (rs1)
rd = [rs1]
A load occurs to address at rs1 with the results loaded to rd.
Misaligned address should cause an exception
* **Verification goals:** Input operands:

All bits of rs1 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P000_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 8.2
* **Feature Description:** lr.w rd, (rs1)
rd = [rs1]
A load occurs to address at rs1 with the results loaded to rd.
Misaligned address should cause an exception
* **Verification goals:** Output result:

All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P000_I002
* **Comments:** 

#### 003 item

* **Requirement location:** Unprivileged ISA
Chapter 8.2
* **Feature Description:** lr.w rd, (rs1)
rd = [rs1]
A load occurs to address at rs1 with the results loaded to rd.
Misaligned address should cause an exception
* **Verification goals:** Exception:

Misaligned address (non-32-bit aligned) will always cause exceptio
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P000_I003
* **Comments:** 

### 001_SC.W sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 8.2
* **Feature Description:** sc.w rd, rs2, (rs1)
[rs1] = rs2
rd = exokay ? 0 : 1
A store occurs to address at rs1  with data from rs2.
If the reservation set from a previous LR.W fails, then rd is set to a non-zero value and the store does not occur.
If the reservation set passes, then rd is set to a zero-value and the store succeeds.
* **Verification goals:** Register operands:

All possible rs1 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P001_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 8.2
* **Feature Description:** sc.w rd, rs2, (rs1)
[rs1] = rs2
rd = exokay ? 0 : 1
A store occurs to address at rs1  with data from rs2.
If the reservation set from a previous LR.W fails, then rd is set to a non-zero value and the store does not occur.
If the reservation set passes, then rd is set to a zero-value and the store succeeds.
* **Verification goals:** Input operands:

All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P001_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 8.2
* **Feature Description:** sc.w rd, rs2, (rs1)
[rs1] = rs2
rd = exokay ? 0 : 1
A store occurs to address at rs1  with data from rs2.
If the reservation set from a previous LR.W fails, then rd is set to a non-zero value and the store does not occur.
If the reservation set passes, then rd is set to a zero-value and the store succeeds.
* **Verification goals:** Output result:

rd is either zero or non-zero to indicate success or failure, respectively
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P001_I002
* **Comments:** 

#### 003 item

* **Requirement location:** Unprivileged ISA
Chapter 8.2
* **Feature Description:** sc.w rd, rs2, (rs1)
[rs1] = rs2
rd = exokay ? 0 : 1
A store occurs to address at rs1  with data from rs2.
If the reservation set from a previous LR.W fails, then rd is set to a non-zero value and the store does not occur.
If the reservation set passes, then rd is set to a zero-value and the store succeeds.
* **Verification goals:** Exception:

Misaligned address (non-32-bit aligned) will always cause exception
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P001_I003
* **Comments:** 

## RV32A Atomic Memory Operations feature

### 000_AMOSWAP.W sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoswap.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2
A load occurs from the address at rs1 into rd.
The value at rs2 is then written back to the address at (rs1)
* **Verification goals:** Input operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoswap.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2
A load occurs from the address at rs1 into rd.
The value at rs2 is then written back to the address at (rs1)
* **Verification goals:** Input operands:

All bits of rs1 are toggled
All bits of rs2 are toggled
Zero and non-zero values of rs2 are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P000_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoswap.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2
A load occurs from the address at rs1 into rd.
The value at rs2 is then written back to the address at (rs1)
* **Verification goals:** Output result: 

All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P000_I002
* **Comments:** 

#### 003 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoswap.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2
A load occurs from the address at rs1 into rd.
The value at rs2 is then written back to the address at (rs1)
* **Verification goals:** Exception:

Misaligned address (non-32-bit aligned) will always cause exception
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P000_I003
* **Comments:** 

### 001_AMOADD.W sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoadd.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 + [rs1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and added using signed arithmetic and the result iis then written back to the address at (rs1)
* **Verification goals:** Input operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P001_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoadd.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 + [rs1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and added using signed arithmetic and the result iis then written back to the address at (rs1)
* **Verification goals:** Input operands:

All bits of rs1 are toggled
All bits of rs2 are toggled
+ve, -ve and zero values of rs2 are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P001_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoadd.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 + [rs1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and added using signed arithmetic and the result iis then written back to the address at (rs1)
* **Verification goals:** Output result: 

+ve, -ve and zero values of rd are used
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P001_I002
* **Comments:** 

#### 003 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoadd.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 + [rs1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and added using signed arithmetic and the result iis then written back to the address at (rs1)
* **Verification goals:** Exception:

Misaligned address (non-32-bit aligned) will always cause exception
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P001_I003
* **Comments:** 

### 002_AMOAND.W sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoand.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 & rs[1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and bit-wise ANDed and the result iis then written back to the address at (rs1)
* **Verification goals:** Input operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P002_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoand.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 & rs[1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and bit-wise ANDed and the result iis then written back to the address at (rs1)
* **Verification goals:** Input operands:

All bits of rs1 are toggled
All bits of rs2 are toggled
Zero and non-zero values of rs2 are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P002_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoand.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 & rs[1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and bit-wise ANDed and the result iis then written back to the address at (rs1)
* **Verification goals:** Output result: 

All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P002_I002
* **Comments:** 

#### 003 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoand.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 & rs[1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and bit-wise ANDed and the result iis then written back to the address at (rs1)
* **Verification goals:** Exception:

Misaligned address (non-32-bit aligned) will always cause exception
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P002_I003
* **Comments:** 

### 003_AMOOR.W sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoor.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 | [rs1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and bit-wise ORed and the result iis then written back to the address at (rs1)
* **Verification goals:** Input operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P003_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoor.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 | [rs1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and bit-wise ORed and the result iis then written back to the address at (rs1)
* **Verification goals:** Input operands:

All bits of rs1 are toggled
All bits of rs2 are toggled
Zero and non-zero values of rs2 are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P003_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoor.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 | [rs1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and bit-wise ORed and the result iis then written back to the address at (rs1)
* **Verification goals:** Output result: 

All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P003_I002
* **Comments:** 

#### 003 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoor.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 | [rs1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and bit-wise ORed and the result iis then written back to the address at (rs1)
* **Verification goals:** Exception:

Misaligned address (non-32-bit aligned) will always cause exception
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P003_I003
* **Comments:** 

### 004_AMOXOR.W sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoxor.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 ^ [rs1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and bit-wise XORRed and the result iis then written back to the address at (rs1)
* **Verification goals:** Input operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P004_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoxor.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 ^ [rs1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and bit-wise XORRed and the result iis then written back to the address at (rs1)
* **Verification goals:** Input operands:

All bits of rs1 are toggled
All bits of rs2 are toggled
Zero and non-zero values of rs2 are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P004_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoxor.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 ^ [rs1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and bit-wise XORRed and the result iis then written back to the address at (rs1)
* **Verification goals:** Output result: 

All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P004_I002
* **Comments:** 

#### 003 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amoxor.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = rs2 ^ [rs1]
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and bit-wise XORRed and the result iis then written back to the address at (rs1)
* **Verification goals:** Exception:

Misaligned address (non-32-bit aligned) will always cause exception
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P004_I003
* **Comments:** 

### 005_AMOMAX.W sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amomax.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = max_signed(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming signed numbers and the largest value is then written back to the address at (rs1)
* **Verification goals:** Input operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P005_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amomax.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = max_signed(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming signed numbers and the largest value is then written back to the address at (rs1)
* **Verification goals:** Input operands:

All bits of rs1 are toggled
All bits of rs2 are toggled
+ve, -ve and zero values of rs2 are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P005_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amomax.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = max_signed(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming signed numbers and the largest value is then written back to the address at (rs1)
* **Verification goals:** Output result: 

+ve, -ve and zero values of rd are used
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P005_I002
* **Comments:** 

#### 003 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amomax.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = max_signed(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming signed numbers and the largest value is then written back to the address at (rs1)
* **Verification goals:** Exception:

Misaligned address (non-32-bit aligned) will always cause exception
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P005_I003
* **Comments:** 

### 006_AMOMAXU.W sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amomaxu.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = max_unsigned(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming unsigned numbers and the largest value is then written back to the address at (rs1)
* **Verification goals:** Input operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P006_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amomaxu.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = max_unsigned(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming unsigned numbers and the largest value is then written back to the address at (rs1)
* **Verification goals:** Input operands:

All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P006_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amomaxu.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = max_unsigned(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming unsigned numbers and the largest value is then written back to the address at (rs1)
* **Verification goals:** Output result: 

All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P006_I002
* **Comments:** 

#### 003 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amomaxu.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = max_unsigned(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming unsigned numbers and the largest value is then written back to the address at (rs1)
* **Verification goals:** Exception:

Misaligned address (non-32-bit aligned) will always cause exception
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P006_I003
* **Comments:** 

### 007_AMOMIN.W sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amomin.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = min_signed(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming signed numbers and the smaller value is then written back to the address at (rs1)
* **Verification goals:** Input operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P007_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amomin.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = min_signed(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming signed numbers and the smaller value is then written back to the address at (rs1)
* **Verification goals:** Input operands:

All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P007_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amomin.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = min_signed(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming signed numbers and the smaller value is then written back to the address at (rs1)
* **Verification goals:** Output result: 

+ve, -ve and zero values of rd are used
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P007_I002
* **Comments:** 

#### 003 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amomin.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = min_signed(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming signed numbers and the smaller value is then written back to the address at (rs1)
* **Verification goals:** Exception:

Misaligned address (non-32-bit aligned) will always cause exception
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P007_I003
* **Comments:** 

### 008_AMOMINU.W sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amominu.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = min_unsigned(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming unsigned numbers and the smaller value is then written back to the address at (rs1)
* **Verification goals:** Input operands:

All possible rs1 registers are used.
All possible rs2 registers are used.
All possible rd registers are used.
All possible register combinations where rs1 == rd are used
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P008_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amominu.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = min_unsigned(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming unsigned numbers and the smaller value is then written back to the address at (rs1)
* **Verification goals:** Input operands:

All bits of rs1 are toggled
All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P008_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amominu.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = min_unsigned(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming unsigned numbers and the smaller value is then written back to the address at (rs1)
* **Verification goals:** Output result: 

All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P008_I002
* **Comments:** 

#### 003 item

* **Requirement location:** Unprivileged ISA
Chapter 8.4
* **Feature Description:** amominu.w rd, rs2, (rs1)
rd = [rs1]
[rs1] = min_unsigned(rs2, [rs1])
A load occurs from the address at rs1 into rd.
The values in rd and rs2 and compared assuming unsigned numbers and the smaller value is then written back to the address at (rs1)
* **Verification goals:** Exception:

Misaligned address (non-32-bit aligned) will always cause exception
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P008_I003
* **Comments:** 

## RV32C Integer Computational Instructions feature

### 000_C.LI sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.li rd, imm[5:0]
x[rd] = sext(imm)
Expands to addi rd, x0, imm[5:0]. Invalid when rd=x0.
rd is calculated using signed arithmetic
* **Verification goals:** Input operands:

All bits of imm[5:0] are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.li rd, imm[5:0]
x[rd] = sext(imm)
Expands to addi rd, x0, imm[5:0]. Invalid when rd=x0.
rd is calculated using signed arithmetic
* **Verification goals:** Output result:

All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P000_I001
* **Comments:** 

### 001_C.LUI sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.lui rd, nzimm[17:12]
x[rd] = sext(nzimm[17:12] << 12)
Expands to lui rd, nzimm[17:12]. Invalid when rd = {x0, x2} or imm = 0.
rd is calculated using signed arithmetic.
* **Verification goals:** Input operands:

All bits of imm[17:12] are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P001_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.lui rd, nzimm[17:12]
x[rd] = sext(nzimm[17:12] << 12)
Expands to lui rd, nzimm[17:12]. Invalid when rd = {x0, x2} or imm = 0.
rd is calculated using signed arithmetic.
* **Verification goals:** Output result:

All bits of rd[31:12] are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P001_I001
* **Comments:** 

### 002_C.ADDI sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.addi rd, nzimm[5:0]
x[rd] = x[rd] + sext(nzimm[5:0])
Expands to addi rd, rd, nzimm[5:0].
Invalid when rd=x0 or nzimm = 0. Arithmetic overflow is lost and ignored.
rd is calculated using signed arithmetic.
* **Verification goals:** Register operands:

All possible rd registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P002_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.addi rd, nzimm[5:0]
x[rd] = x[rd] + sext(nzimm[5:0])
Expands to addi rd, rd, nzimm[5:0].
Invalid when rd=x0 or nzimm = 0. Arithmetic overflow is lost and ignored.
rd is calculated using signed arithmetic.
* **Verification goals:** Input operands:

All inputs bits of rd before instruction execution are toggled
All bits of nzimm are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P002_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.addi rd, nzimm[5:0]
x[rd] = x[rd] + sext(nzimm[5:0])
Expands to addi rd, rd, nzimm[5:0].
Invalid when rd=x0 or nzimm = 0. Arithmetic overflow is lost and ignored.
rd is calculated using signed arithmetic.
* **Verification goals:** Output result:

All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P002_I002
* **Comments:** 

### 003_C.ADDI16SP sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.addi16sp nzimm[9:4]
x[2] = x[2] + sext(nzimm[9:4])
Expands to addi x2, x2, nzimm[9:4]. Invalid when nzimm=0.
rd is calculated using signed arithmetic.
* **Verification goals:** Input operands:

+ve and -ve values of nzimm are used
All bits of nzimm[9:4] are toggled
All bits of x2 before instruction execution are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P003_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.addi16sp nzimm[9:4]
x[2] = x[2] + sext(nzimm[9:4])
Expands to addi x2, x2, nzimm[9:4]. Invalid when nzimm=0.
rd is calculated using signed arithmetic.
* **Verification goals:** Output result:

All bits of x2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P003_I001
* **Comments:** 

### 004_C.ADDI4SPN sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.addi4spn rd', nzuimm[9:2]
x[8+rd'] = x[2] + nzuimm[9:2]
Expands to addi rd', x2, nzuimm[9:2]. Invalid when nzuimm = 0.
rd is calculated using signed arithmetic.
* **Verification goals:** Register operands:

All possible rd` registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P004_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.addi4spn rd', nzuimm[9:2]
x[8+rd'] = x[2] + nzuimm[9:2]
Expands to addi rd', x2, nzuimm[9:2]. Invalid when nzuimm = 0.
rd is calculated using signed arithmetic.
* **Verification goals:** Input operands:

All bits of nzuimm[9:2] are toggled
All bits of x2 before instruction execution are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P004_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.addi4spn rd', nzuimm[9:2]
x[8+rd'] = x[2] + nzuimm[9:2]
Expands to addi rd', x2, nzuimm[9:2]. Invalid when nzuimm = 0.
rd is calculated using signed arithmetic.
* **Verification goals:** Output result:

All bits of rd` are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P004_I002
* **Comments:** 

### 005_C.SLLI sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.slli rd, uimm[5:0]
x[rd] = x[rd] << uimm[5:0]
Expands to slli rd, rd, uimm[5:0]. Invalid when uimm[5] = 1, or uimm=0, or rd=x0.
* **Verification goals:** Register operands:

All possible rd registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P005_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.slli rd, uimm[5:0]
x[rd] = x[rd] << uimm[5:0]
Expands to slli rd, rd, uimm[5:0]. Invalid when uimm[5] = 1, or uimm=0, or rd=x0.
* **Verification goals:** Input operands:

All shift amounts from [0:31] are used
All bits of rd before instruction execution are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P005_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.slli rd, uimm[5:0]
x[rd] = x[rd] << uimm[5:0]
Expands to slli rd, rd, uimm[5:0]. Invalid when uimm[5] = 1, or uimm=0, or rd=x0.
* **Verification goals:** Output result:

All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P005_I002
* **Comments:** 

### 006_C.SRLI sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.srli rd', uimm[5:0]
x[8+rd'] = x[8+rd'] >>u uimm[5:0]
Expands to srli rd', rd', uimm[5:0]. Invalid when uimm[5] = 1, or uimm=0,
* **Verification goals:** Register operands:

All possible rd` registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P006_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.srli rd', uimm[5:0]
x[8+rd'] = x[8+rd'] >>u uimm[5:0]
Expands to srli rd', rd', uimm[5:0]. Invalid when uimm[5] = 1, or uimm=0,
* **Verification goals:** Input operands:

All shift amounts from [0:31] are used
All bits of rd before instruction execution are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P006_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.srli rd', uimm[5:0]
x[8+rd'] = x[8+rd'] >>u uimm[5:0]
Expands to srli rd', rd', uimm[5:0]. Invalid when uimm[5] = 1, or uimm=0,
* **Verification goals:** Output result:

All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P006_I002
* **Comments:** 

### 007_C.SRAI sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.srai rd', uimm[5:0]
x[8+rd'] = x[8+rd'] >> uimm[5:0]
Expands to srai rd', rd', uimm[5:0].
* **Verification goals:** Register operands:

All possible rd` registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P007_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.srai rd', uimm[5:0]
x[8+rd'] = x[8+rd'] >> uimm[5:0]
Expands to srai rd', rd', uimm[5:0].
* **Verification goals:** Input operands:

All shift amounts from [0:31] are used
+ve, -ve and zero values of rd` are used
All bits of rd` before instruction execution are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P007_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.srai rd', uimm[5:0]
x[8+rd'] = x[8+rd'] >> uimm[5:0]
Expands to srai rd', rd', uimm[5:0].
* **Verification goals:** Output result:

All bits of rd` are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P007_I002
* **Comments:** 

### 008_C.ANDI sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.andi rd', imm[5:0]
x[8+rd'] = x[8+rd'] & sext(imm[5:0])
Expands to andi rd', rd', imm[5:0].
imm treated as signed number
* **Verification goals:** Register operands:

All possible rd` registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P008_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.andi rd', imm[5:0]
x[8+rd'] = x[8+rd'] & sext(imm[5:0])
Expands to andi rd', rd', imm[5:0].
imm treated as signed number
* **Verification goals:** Input operands:

All shift amounts from [0:31] are used
+ve, -ve and zero values of imm are used
All bits of rd` before instruction execution are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P008_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.andi rd', imm[5:0]
x[8+rd'] = x[8+rd'] & sext(imm[5:0])
Expands to andi rd', rd', imm[5:0].
imm treated as signed number
* **Verification goals:** Output result:

All bits of rd` are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P008_I002
* **Comments:** 

### 009_C.MV sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.mv rd, rs2
x[rd] = x[rs2]
Expands to add rd, x0, rs2
Invalid when rs2=x0 or rd=x0.
* **Verification goals:** Register operands:

All possible rd registers are used.
All possible register combinations where rs2 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P009_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.mv rd, rs2
x[rd] = x[rs2]
Expands to add rd, x0, rs2
Invalid when rs2=x0 or rd=x0.
* **Verification goals:** Input operands:

All bits of rs2 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P009_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.mv rd, rs2
x[rd] = x[rs2]
Expands to add rd, x0, rs2
Invalid when rs2=x0 or rd=x0.
* **Verification goals:** Output result:

All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P009_I002
* **Comments:** 

### 010_C.ADD sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.add rd, rs2
x[rd] = x[rd] + x[rs2]
Expands to add rd, rd, rs2. Invalid when rd=x0 or rs2=x0.
Arithmetic overflow is lost and ignored
* **Verification goals:** Register operands:

All possible rd registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P010_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.add rd, rs2
x[rd] = x[rd] + x[rs2]
Expands to add rd, rd, rs2. Invalid when rd=x0 or rs2=x0.
Arithmetic overflow is lost and ignored
* **Verification goals:** Input operands:

+ve,-ve and zero values of rs2 are used
+ve,-ve, and zero values of rdrs1 are used
All bits of rs2 are toggled
All bits of rd before instruction execution are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P010_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.add rd, rs2
x[rd] = x[rd] + x[rs2]
Expands to add rd, rd, rs2. Invalid when rd=x0 or rs2=x0.
Arithmetic overflow is lost and ignored
* **Verification goals:** Output result:

All bits of rd are toggled
+ve,-ve and zero values of rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P010_I002
* **Comments:** 

### 011_C.AND sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.and rd', rs2'
x[8+rd'] = x[8+rd'] & x[8+rs2']
Expands to and rd', rd', rs2'.
* **Verification goals:** Register operands:

All possible rd` registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P011_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.and rd', rs2'
x[8+rd'] = x[8+rd'] & x[8+rs2']
Expands to and rd', rd', rs2'.
* **Verification goals:** Input operands:

Non-zero and zero values of rs2` are used
Non-zero and zero values of rd` are used
All bits of rs2` are toggled
All bits of rd` before instruction execution are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P011_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.and rd', rs2'
x[8+rd'] = x[8+rd'] & x[8+rs2']
Expands to and rd', rd', rs2'.
* **Verification goals:** Output result:

All bits of rd` are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P011_I002
* **Comments:** 

### 012_C.OR sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.or rd', rs2'
x[8+rd'] = x[8+rd'] | x[8+rs2']
Expands to or rd', rd', rs2'.
* **Verification goals:** Register operands:

All possible rd` registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P012_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.or rd', rs2'
x[8+rd'] = x[8+rd'] | x[8+rs2']
Expands to or rd', rd', rs2'.
* **Verification goals:** Input operands:

Non-zero and zero values of rs2` are used
Non-zero and zero values of rd` are used
All bits of rs2` are toggled
All bits of rd` before instruction execution are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P012_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.or rd', rs2'
x[8+rd'] = x[8+rd'] | x[8+rs2']
Expands to or rd', rd', rs2'.
* **Verification goals:** Output result:

All bits of rd` are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P012_I002
* **Comments:** 

### 013_C.XOR sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.xor rd', rs2'
x[8+rd'] = x[8+rd'] ^ x[8+rs2']
Expands to xor rd', rd', rs2'.
* **Verification goals:** Register operands:

All possible rd` registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P013_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.xor rd', rs2'
x[8+rd'] = x[8+rd'] ^ x[8+rs2']
Expands to xor rd', rd', rs2'.
* **Verification goals:** Input operands:

Non-zero and zero values of rs2` are used
Non-zero and zero values of rd` are used
All bits of rs2` are toggled
All bits of rd` before instruction execution are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P013_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.xor rd', rs2'
x[8+rd'] = x[8+rd'] ^ x[8+rs2']
Expands to xor rd', rd', rs2'.
* **Verification goals:** Output result:

All bits of rd` are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P013_I002
* **Comments:** 

### 014_C.SUB sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.sub rd', rs2'
x[8+rd'] = x[8+rd'] - x[8+rs2']
Expands to sub rd', rd', rs2'. Arithmetic underflow is ignored
* **Verification goals:** Register operands:

All possible rd` registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P014_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.sub rd', rs2'
x[8+rd'] = x[8+rd'] - x[8+rs2']
Expands to sub rd', rd', rs2'. Arithmetic underflow is ignored
* **Verification goals:** Input operands:

+ve,-ve and zero values of rs2` are used
+ve, -ve, and zero values of rd` are used
All bits of rs2` are toggled
All bits of rd` before instruction execution are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P014_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.sub rd', rs2'
x[8+rd'] = x[8+rd'] - x[8+rs2']
Expands to sub rd', rd', rs2'. Arithmetic underflow is ignored
* **Verification goals:** Output result:

All bits of rd` are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P014_I002
* **Comments:** 

### 015_C.EBREAK sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.5
* **Feature Description:** c.ebreak
RaiseException(Breakpoint)
Expands to ebreak.
* **Verification goals:** Instruction executed
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P015_I000
* **Comments:** 

## RV32C Control Transfer Instructions feature

### 000_C.J sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.4
* **Feature Description:** c.j imm[11:1]
pc += sext(imm)
pc is calculated using signed arithmetic
Expands to jal x0, imm[11:1].
* **Verification goals:** Input operands:

uimm value is non-zero and zero
All bits of uimm are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP010_P000_I000
* **Comments:** 

### 001_C.JAL sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.4
* **Feature Description:** c.jal imm[11:1]
x[1] = pc+2; pc += sext(imm)
pc is calculated using signed arithmetic.
* **Verification goals:** Input operands:

uimm value is non-zero and zero
All bits of uimm are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP010_P001_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.4
* **Feature Description:** c.jal imm[11:1]
x[1] = pc+2; pc += sext(imm)
pc is calculated using signed arithmetic.
* **Verification goals:** Output result:

All bits of x1 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP010_P001_I001
* **Comments:** 

### 002_C.JR sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.4
* **Feature Description:** c.jr rs1
pc = x[rs1]
Expands to jalr x0, 0(rs1). 
Invalid when rs1=x0.
* **Verification goals:** Register operands:

All possible rs1 registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP010_P002_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.4
* **Feature Description:** c.jr rs1
pc = x[rs1]
Expands to jalr x0, 0(rs1). 
Invalid when rs1=x0.
* **Verification goals:** Input operands:

All bits of rs1 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP010_P002_I001
* **Comments:** 

### 003_C.JALR sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.4
* **Feature Description:** c.jalr rs1
t = pc + 2; pc = x[rs1]; x[1] = t
Expands to jalr x1, 0(rs1). 
Invalid when rs1=x0.
* **Verification goals:** Register operands:

All possible rs1 registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP010_P003_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.4
* **Feature Description:** c.jalr rs1
t = pc + 2; pc = x[rs1]; x[1] = t
Expands to jalr x1, 0(rs1). 
Invalid when rs1=x0.
* **Verification goals:** Input operands:

All bits of rs1 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP010_P003_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.4
* **Feature Description:** c.jalr rs1
t = pc + 2; pc = x[rs1]; x[1] = t
Expands to jalr x1, 0(rs1). 
Invalid when rs1=x0.
* **Verification goals:** Output result:

All bits of x1 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP010_P003_I002
* **Comments:** 

### 004_C.BEQZ sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.4
* **Feature Description:** c.beqz rs1', imm[8:1]
if (x[8+rs1'] == 0) pc += sext(imm)
Expands to beq rs1', x0, imm[8:1]. pc is calculated using signed arithmetic.
* **Verification goals:** Register operands:

All possible rs1` registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP010_P004_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.4
* **Feature Description:** c.beqz rs1', imm[8:1]
if (x[8+rs1'] == 0) pc += sext(imm)
Expands to beq rs1', x0, imm[8:1]. pc is calculated using signed arithmetic.
* **Verification goals:** Input operands:

All bits of rs1` are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP010_P004_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.4
* **Feature Description:** c.beqz rs1', imm[8:1]
if (x[8+rs1'] == 0) pc += sext(imm)
Expands to beq rs1', x0, imm[8:1]. pc is calculated using signed arithmetic.
* **Verification goals:** Output result:

Branch taken or not-taken
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP010_P004_I002
* **Comments:** 

### 005_C.BNEZ sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.4
* **Feature Description:** c.bnez  rs1', imm[8:1]
if (x[8+rs1'] ≠ 0) pc += sext(imm)
Expands to bne rs1', x0, imm[8:1]. pc is calculated using signed arithmetic.
* **Verification goals:** Register operands:

All possible rs1` registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP010_P005_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.4
* **Feature Description:** c.bnez  rs1', imm[8:1]
if (x[8+rs1'] ≠ 0) pc += sext(imm)
Expands to bne rs1', x0, imm[8:1]. pc is calculated using signed arithmetic.
* **Verification goals:** Input operands:

All bits of rs1 are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP010_P005_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.4
* **Feature Description:** c.bnez  rs1', imm[8:1]
if (x[8+rs1'] ≠ 0) pc += sext(imm)
Expands to bne rs1', x0, imm[8:1]. pc is calculated using signed arithmetic.
* **Verification goals:** Output result:

Branch taken or not-taken
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP010_P005_I002
* **Comments:** 

## RV32C Load and Store Instructions feature

### 000_C.LWSP sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.3
* **Feature Description:** c.lwsp rd, uimm(x2)
x[rd] = sext(M[x[2] + uimm][0:31])
Expands to lw rd, uimm[7:2](x2). 
Invalid when rd=x0.
uimm treated as unsigned number
* **Verification goals:** Register operands:

All possible rd registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.3
* **Feature Description:** c.lwsp rd, uimm(x2)
x[rd] = sext(M[x[2] + uimm][0:31])
Expands to lw rd, uimm[7:2](x2). 
Invalid when rd=x0.
uimm treated as unsigned number
* **Verification goals:** Input operands:

uimm value is non-zero and zero
All bits of uimm are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P000_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.3
* **Feature Description:** c.lwsp rd, uimm(x2)
x[rd] = sext(M[x[2] + uimm][0:31])
Expands to lw rd, uimm[7:2](x2). 
Invalid when rd=x0.
uimm treated as unsigned number
* **Verification goals:** Output result:

rd value is non-zero and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P000_I002
* **Comments:** 

### 001_C.SWSP sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.3
* **Feature Description:** c.swsp rs2, uimm(x2)
M[x[2] + uimm][0:31] = x[rs2]
Expands to sw rs2, uimm[7:2](x2).
uimm treated as unsigned number
* **Verification goals:** Register operands:

All possible rs2 registers are used.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P001_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.3
* **Feature Description:** c.swsp rs2, uimm(x2)
M[x[2] + uimm][0:31] = x[rs2]
Expands to sw rs2, uimm[7:2](x2).
uimm treated as unsigned number
* **Verification goals:** Input operands:

uimm value is non-zero and zero
All bits of uimm are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P001_I001
* **Comments:** 

### 002_C.LW sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.3
* **Feature Description:** c.lw rd', uimm(rs1')
x[rd] = sext(M[x[rs1] + uimm][0:31]), where rd=8+rd' and rs1=8+rs1'
Expands to lw rd', uimm[6:2](rs1')
* **Verification goals:** Register operands:

All possible rs1` registers are used.
All possible rd` registers are used.
All possible register combinations where rs1` == rd` are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P002_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.3
* **Feature Description:** c.lw rd', uimm(rs1')
x[rd] = sext(M[x[rs1] + uimm][0:31]), where rd=8+rd' and rs1=8+rs1'
Expands to lw rd', uimm[6:2](rs1')
* **Verification goals:** Input operands:

uimm value is non-zero and zero
All bits of uimm are toggled
All bits of rs1` are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P002_I001
* **Comments:** 

#### 002 item

* **Requirement location:** Unprivileged ISA
Chapter 16.3
* **Feature Description:** c.lw rd', uimm(rs1')
x[rd] = sext(M[x[rs1] + uimm][0:31]), where rd=8+rd' and rs1=8+rs1'
Expands to lw rd', uimm[6:2](rs1')
* **Verification goals:** Output result:

rd` value is non-zero and zero
All bits of rd are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P002_I002
* **Comments:** 

### 003_C.SW sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 16.3
* **Feature Description:** c.sw rs2', uimm(rs1')
M[x[rs1] + uimm][0:31] = x[rs2], where rs2=8+rs2' and rs1=8+rs1'
Expands to sw rs2', uimm[6:2](rs1').
* **Verification goals:** Register operands:

All possible rs1` registers are used.
All possible rd` registers are used.
All possible register combinations where rs1` == rd` are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P003_I000
* **Comments:** 

#### 001 item

* **Requirement location:** Unprivileged ISA
Chapter 16.3
* **Feature Description:** c.sw rs2', uimm(rs1')
M[x[rs1] + uimm][0:31] = x[rs2], where rs2=8+rs2' and rs1=8+rs1'
Expands to sw rs2', uimm[6:2](rs1').
* **Verification goals:** Input operands:

uimm value is non-zero and zero
All bits of uimm are toggled
All bits of rs1` are toggled
All bits of rs2` are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP009_P003_I001
* **Comments:** 

## RV32Zicsr Control and Status Register (CSR) Instructions feature

### 000_CSRRW sub-feature

#### 000 item

* **Requirement location:** ISA Chapter 9
* **Feature Description:** csrrw rd, rs1, csr
rd = Zext([csr]); csr = [rs1]
* **Verification goals:** Register operands:

All possible rs1 registers are used
All possible rd registers are used
All supported CSRs are used
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA Chapter 9
* **Feature Description:** csrrw rd, rs1, csr
rd = Zext([csr]); csr = [rs1]
* **Verification goals:** Input operand:

Non-zero and zero rs1 operands are used (if rs1 != x0)
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P000_I001
* **Comments:** 

### 001_CSRRS sub-feature

#### 000 item

* **Requirement location:** ISA Chapter 9
* **Feature Description:** csrrs rd, rs1, csr
rd = Zext([csr]); csr = [rs1] | csr
Note that not all bits of csr will be writable.
* **Verification goals:** Register operands:

All possible rs1 registers are used
All possible rd registers are used
All supported CSRs are used
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P001_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA Chapter 9
* **Feature Description:** csrrs rd, rs1, csr
rd = Zext([csr]); csr = [rs1] | csr
Note that not all bits of csr will be writable.
* **Verification goals:** Input operand:

Non-zero and zero rs1 operands are used (if rs1 != x0)
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P001_I001
* **Comments:** 

### 002_CSRRC sub-feature

#### 000 item

* **Requirement location:** ISA Chapter 9
* **Feature Description:** csrrs rd, rs1, csr
rd = Zext([csr]); csr = ~[rs1] | csr
Note that not all bits of csr will be writable.
* **Verification goals:** Register operands:

All possible rs1 registers are used
All possible rd registers are used
All supported CSRs are used
All possible register combinations where rs1 == rd are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P002_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA Chapter 9
* **Feature Description:** csrrs rd, rs1, csr
rd = Zext([csr]); csr = ~[rs1] | csr
Note that not all bits of csr will be writable.
* **Verification goals:** Input operand:

Non-zero and zero rs1 operands are used (if rs1 != x0)
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P002_I001
* **Comments:** 

### 003_CSRRWI sub-feature

#### 000 item

* **Requirement location:** ISA Chapter 9
* **Feature Description:** csrrwi rd, imm[4:0], csr
rd = Zext([csr]); csr = Zext(imm[4:0])
If rd == x0 then CSR is not read.
* **Verification goals:** Register operands:

All possible rd registers are used
All supported CSRs are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P003_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA Chapter 9
* **Feature Description:** csrrwi rd, imm[4:0], csr
rd = Zext([csr]); csr = Zext(imm[4:0])
If rd == x0 then CSR is not read.
* **Verification goals:** Input operand:

Non-zero and zero imm[4:0] operands are used
All bits of imm[4:0] are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P003_I001
* **Comments:** 

### 004_CSRRSI sub-feature

#### 000 item

* **Requirement location:** ISA Chapter 9
* **Feature Description:** csrrsi rd, imm[4:0], csr
rd = Zext([csr]); csr = Zext(imm[4:0]) | csr
Note that not all bits of csr will be writable.
* **Verification goals:** Register operands:

All possible rd registers are used
All supported CSRs are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P004_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA Chapter 9
* **Feature Description:** csrrsi rd, imm[4:0], csr
rd = Zext([csr]); csr = Zext(imm[4:0]) | csr
Note that not all bits of csr will be writable.
* **Verification goals:** Input operand:

Non-zero and zero imm[4:0] operands are used
All bits of imm[4:0] are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P004_I001
* **Comments:** 

### 005_CSRRCI sub-feature

#### 000 item

* **Requirement location:** ISA Chapter 9
* **Feature Description:** csrrs rd, imm[4:0], csr
rd = Zext([csr]); csr = ~(Zext(imm[4:0])) | csr
Note that not all bits of csr will be writable.
* **Verification goals:** Register operands:

All possible rd registers are used
All supported CSRs are used
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P005_I000
* **Comments:** 

#### 001 item

* **Requirement location:** ISA Chapter 9
* **Feature Description:** csrrs rd, imm[4:0], csr
rd = Zext([csr]); csr = ~(Zext(imm[4:0])) | csr
Note that not all bits of csr will be writable.
* **Verification goals:** Input operand:

Non-zero and zero imm[4:0] operands are used
All bits of imm[4:0] are toggled
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P005_I001
* **Comments:** 

## RV32Zifencei Instruction-Fetch Fence feature

### 000_FENCE.I sub-feature

#### 000 item

* **Requirement location:** Unprivileged ISA
Chapter 3
* **Feature Description:** Fence.I instruction executed
Implementation is core-specific
* **Verification goals:** Fence.I instruction is executed
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP006_P000_I000
* **Comments:** 

