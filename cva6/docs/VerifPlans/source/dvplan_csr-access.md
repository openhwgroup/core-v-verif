# Module: CSR ACCESS VERIFICATION

## Feature: CVA6_Machine_mode_RW_CSRs(mstatus, misa, mideleg, medeleg, mie, mtvec, mcounteren, mepc, mcause, mtval, mip,)

### Sub-feature: 000_Power-on-reset (POR) values of CSR

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Upon reset, RISC-V CVA6 Machine mode RW CSRs must initialize to their respective POR value.
* **Verification Goals**
  
  Verify that the Machine Mode RW CSR POR value must match with the value specified in the RISC-V CVA6 user manual.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_CSR_VERIFICATION_F000_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 001_CSR write and read operations

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  check the correctness of RISCV CVA6 Machine Mode RW CSRs by writing random values like 0xa5a5a5a5, 0x5a5a5a5a, 0xffa1ae40.. and read using the CSR instructions defined in the instruction set architecture (ISA).
* **Verification Goals**
  
  1.Verify that CSR can be written using the appropriate CSR write instructions.  
    
  2.Ensure correct read operations using CSR read instructions.  
     
  3.Ensure that read values of the CSR should be as per CVA6 user manual
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_CSR_VERIFICATION_F000_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 002_CSR access in different privilege modes

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Accessing RISC-V CVA6 Machine Mode CSR in different privilege modes (User, Supervisor and Machine modes).
* **Verification Goals**
  
  1.Ensure that Machine mode CSR can only be accessed in the correct privilege mode according to the specification.  
    
  2.Verify that trying to access Machine Mode CSR in an incorrect privilege mode raises an illegal instruction exception.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_CSR_VERIFICATION_F000_S002_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 003_Testing CSR with inverted reset value



#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  This test scnerio involves applying inverted reset values on CSR during the system reset process.
* **Verification Goals**
  
  To verify system's performance and stability when when inverted reset value are applied on CSR.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_csr-access_F000_S003_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
## Feature: CVA6_Machine_mode_RO_CSRs(mvendorid, marchid, mimpid, mhartid)

### Sub-feature: 000_Power-on-reset (POR) values of CSR

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Upon reset,  RISC-V CVA6 Machine RO(read only) CSR must initialize to their respective POR value.
* **Verification Goals**
  
  Verify that the Machine RO(Read only) CSR POR value must match with the value specified in the RISC-V CVA6 User Manual.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_CSR_VERIFICATION_F001_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 001_CSR write and read operations

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Check the correctness of RISCV CVA6 read only CSR by writing random values like 0xa5a5a5a5, 0x5a5a5a5a, 0xffa1ae40.. and read using the CSR instructions defined in the instruction set architecture (ISA).
* **Verification Goals**
  
  Ensure that write into Machine read-only CSR raises an illegal instruction exception.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_CSR_VERIFICATION_F001_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 002_CSR access in different privilege modes

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Accessing RISC-V Machine read only CSR in different privilege modes (User, Supervisor and Machine modes).
* **Verification Goals**
  
  1.Ensure that Machine read only CSR can only be accessed in the correct privilege mode according to the specification.  
    
  2.Verify that trying to access a Machine read only CSR in an incorrect privilege mode raises an illegal instruction exception.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_CSR_VERIFICATION_F001_S002_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 003_Testing CSR with inverted reset value


#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  This test scnerio involves applying inverted reset values on CSR during the system reset process.
* **Verification Goals**
  
  To verify system's performance and stability when when inverted reset value are applied on CSR.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_csr-access_F001_S003_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
## Feature: CVA6_Supervisor_mode_RW_CSRs(sstatus,stvec, sip, sie, scounteren, sscratch, sepc, scause, stval, satp, pmpaddr[0..7], pmpcfg[0..1])

### Sub-feature: 000_Power-on-reset (POR) values of CSR

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Upon reset, RISC-V CVA6 Supervisor mode RW CSR must initialize to their respective POR value.
* **Verification Goals**
  
  Verify that the Supervisor Mode RW CSR POR value must match with the value specified in the RISC-V CVA6 user manual.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_CSR_VERIFICATION_F002_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 001_CSR write and read operations

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Check the correctness of RISCV CVA6 Supervisor Mode RW CSR by writing random values like 0xa5a5a5a5, 0x5a5a5a5a, 0xffa1ae40.. and read using the CSR instructions defined in the instruction set architecture (ISA).
* **Verification Goals**
  
  1.Verify that CSR can be written using the appropriate CSR write instructions.  
  2.Ensure correct read operations using CSR read instructions.  
   3.Ensure that read values of the CSR should be as per CVA6 user manual.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_CSR_VERIFICATION_F002_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 002_CSR access in different privilege modes

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Accessing RISC-V CVA6 Supervisor Mode CSR in different privilege modes (User,Supervisor and Machine modes).
* **Verification Goals**
  
  1.Ensure that Supervisor Mode CSR can only be accessed in the correct privilege mode according to the specification.  
  2.Verify that trying to access a Supervisor Mode CSR in an incorrect privilege mode raises an illegal instruction exception.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_CSR_VERIFICATION_F002_S002_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 003_Testing CSR with inverted reset value


#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  This test scnerio involves applying inverted reset values on CSR during the system reset process.
* **Verification Goals**
  
  To verify system's performance and stability when when inverted reset value are applied on CSR.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_csr-access_F002_S003_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
## Feature: User_Mode_Counter_CSRs(cycle, instret, cycleh, instreth)

### Sub-feature: 000_Power-on-reset (POR) values of CSR

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Upon reset, RISC-V CVA6 User mode counter CSRs must initialize to their respective POR value.
* **Verification Goals**
  
  Verify that the User Mode counter CSR POR value must match with the value specified in the RISC-V CVA6 user manual.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_CSR_VERIFICATION_F003_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 001_Counter _CSRs_functionality_checking

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  This feature pertains to the verification of functionality of RISC-V cycle, cycleh, instret and instreth Control Status Register (CSR). In a RISC-V architecture  
    
  1.’cycle’ and ‘mcycleh’ are user-level CSR that hold low 32 bits and high 32 bits respectively of the count of clock cycles executed by the processor.  
  2.’instret’ and ‘instreth’ are also user-level CSR that count the total number of instructions executed by the processor.  
     
  The functionality of user mode counter CSR is being tested by performing two continuous reads and checking whether the value in the second read is greater than the value in the first read.
* **Verification Goals**
  
  1.Verify that these CSR are properly initialized.  
  2.Initiate a second read from the counter CSR immediately after the first read.  
  3.Verify that the value of the second read from counter CSR is greater than the value of the initial read.  
  4.Confirm that counter CSRs are correctly incrementing.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_CSR_VERIFICATION_F003_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 002_CSR access in different privilege modes

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Accessing RISC-V CVA6 user Mode counter CSR in different privilege modes (User, Supervisor and Machine modes).
* **Verification Goals**
  
  Ensure that User mode counter CSR can be accessed in all privilege modes by configuring scounteren and mcounteren CSRs as per riscv specification.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_CSR_VERIFICATION_F003_S002_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 003_Testing CSR with inverted reset value


#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  This test scnerio involves applying inverted reset values on CSR during the system reset process.
* **Verification Goals**
  
  To verify system's performance and stability when when inverted reset value are applied on CSR.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_csr-access_F003_S003_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
## Feature: Machine_mode_counter_csr(mcycle,mcycleh,minstret,minstreth)

### Sub-feature: 000_Power-on-reset (POR) values of CSR

#### Item: 000

* **Requirement location:**  https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Upon reset, RISC-V CVA6 User mode counter CSRs must initialize to their respective POR value.
* **Verification Goals**
  
   Verify that the User Mode counter CSR POR value must match with the value specified in the RISC-V CVA6 user manual.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_csr-access_F004_S000_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 001_Counter _CSRs_functionality_checking


#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  This feature pertains to the verification of functionality of RISC-V mcycle, mcycleh, minstret and minstreth Control Status Register (CSR). In a RISC-V architecture  
    
  1.’mcycle’ and ‘mcycleh’ are user-level CSR that hold low 32 bits and high 32 bits respectively of the count of clock cycles executed by the processor.  
  2.’minstret’ and ‘minstreth’ are also user-level CSR that count the total number of instructions executed by the processor.  
    
  The functionality of machine mode counter CSR is being tested by performing two continuous reads and checking whether the value in the second read is greater than the value in the first read.
* **Verification Goals**
  
  1.Verify that these CSR are properly initialized.  
  2.Initiate a second read from the counter CSR immediately after the first read.  
  3.Verify that the value of the second read from counter CSR is greater than the value of the initial read.  
  4.Confirm that counter CSRs are correctly incrementing.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_csr-access_F004_S001_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 002_CSR access in different privilege modes

#### Item: 000

* **Requirement location:** https://docs.openhwgroup.org/projects/cva6-user-manual/01_cva6_user/CV32A6_Control_Status_Registers.html
* **Feature Description**
  
  Accessing RISC-V CVA6 user Machine mode counter CSR in different privilege modes (User, Supervisor and Machine modes).
* **Verification Goals**
  
  1.Ensure that Machine mode CSR can only be accessed in the correct privilege mode according to the specification.  
  2.Verify that trying to access Machine Mode CSR in an incorrect privilege mode raises an illegal instruction exception.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_csr-access_F004_S002_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
### Sub-feature: 003_Testing CSR with inverted RESET value

#### Item: 000

* **Requirement location:** 
* **Feature Description**
  
  This test scnerio involves applying inverted reset values on CSR during the system reset process.
* **Verification Goals**
  
  To verify system's performance and stability when when inverted reset value are applied on CSR.
* **Pass/Fail Criteria:** Self-Check
* **Test Type:** Directed SelfChk
* **Coverage Method:** Functional Coverage
* **Applicable Cores:** CV32A6_v0.1.0
* **Unique verification tag:** VP_csr-access_F004_S003_I000
* **Link to Coverage:** 
* **Comments**
  
  *(none)*  
  
