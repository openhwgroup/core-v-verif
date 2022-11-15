# Module: perf_counter

## Feature: Writing into mhpmevent[8:3] CSR

### Sub-feature: 000_Triggering mhpmevent8-mhpmevent3 CSR events

#### Item: 000

* **Requirement location:** CVA6 performance counter
* **Feature Description**   
  The event selector CSR's mhpmevent8-mhpmevent3 defines which of the events are to be counted by the generic counter.
* **Verification goals**   
  To monitor events on the performance counter by writing into mhpmevent8-mhpmevent3 CSR's.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** Constrained Random
* **Coverage Method:** Code Coverage
* **Applicable Cores:** CV32A6-step1, CV64A6-step3
* **Link to Coverage:** VP_IP000_P000_I000
* **Comments:** 

## Feature: writing into mhpmcounter[8:3] CSR

### Sub-feature: 000_Assigning values to generic counter

#### Item: 000

* **Requirement location:** CVA6 performance counter
* **Feature Description**   
  Assigning lower 32 or 64-bit value to generic counter
* **Verification goals**   
  If XLEN=32, writes mhpmcounter8-mhpmcounter3 CSRs to assign lower 32-bit(31-0) value to a generic counter.  
  else if XLEN=64, assign 64-bit value to generic counter by writing into mhpmcounter CSR's.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** Constrained Random
* **Coverage Method:** Code Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP001_P000_I000
* **Comments:** 

## Feature: writing into mhpmcounter[8:3]h CSR

### Sub-feature: 000_Assigning value to generic counter

#### Item: 000

* **Requirement location:** CVA6 performance counter
* **Feature Description**   
  Assigning value to a generic counter by writing into mhpmcounter8h-mhpmcounter3h csr
* **Verification goals**   
  If XLEN=32, writes mhpmcounter8h-mhpmcounter3h CSRs to assign upper 32-bit(63-32) value to a generic counter.  
  else if XLEN=64, it will raise update_access_exception to 1.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** Constrained Random
* **Coverage Method:** Code Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP002_P000_I000
* **Comments:** 

## Feature: Reading mhpmcounter[8:3] CSR

### Sub-feature: 000_Reading counter values

#### Item: 000

* **Requirement location:** CVA6 performance counter
* **Feature Description**   
  Reading generic counter values by reading mhpmcounter8-mhpmcounter3 CSR.
* **Verification goals**   
  XLEN=32, Reads mhpmcounter8-mhpmcounter3 CSRs return bits 31-0 of the corresponding counter.  
  else if XLEN=64, Reads mhpmcounter8-mhpmcounter3 CSRs return bits 63-0 of the corresponding counter.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** Constrained Random
* **Coverage Method:** Code Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP003_P000_I000
* **Comments:** 

## Feature: Reading mhpmcounter[8:3]h CSR

### Sub-feature: 000_Reading counter values

#### Item: 000

* **Requirement location:** CVA6 performance counter
* **Feature Description**   
  Reading generic counter values by reading mhpmcounter8h-mhpmcounter3h CSR.
* **Verification goals**   
  XLEN=32, Reads mhpmcounter8h-mhpmcounter3h CSRs return bits 63-32 of the corresponding counter.  
  else if XLEN=64, it will raise read_access_excemption to 1.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** Constrained Random
* **Coverage Method:** Code Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP004_P000_I000
* **Comments:** 

## Feature: Reading mhpmevent[8:3]

### Sub-feature: 000_Reading mhpmevent[8:3] CSR

#### Item: 000

* **Requirement location:** CVA6 performance counter
* **Feature Description**   
  Reading mhpmevent8-mhpmevent3 CSR
* **Verification goals**   
  Reading mhpmevent[8:3] value by reading into mhpmevent8-mhpmevent3 CSR.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** Constrained Random
* **Coverage Method:** Code Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP005_P000_I000
* **Comments:** 

