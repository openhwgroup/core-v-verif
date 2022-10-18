# AXI module

## Burst feature

### 000_Control_Signals sub-feature

#### 000 item

* **Requirement location:** AXI Design doc - Address structure
* **Feature Description:** All transaction performed by CVA6 are of type INCR. AxBURST = 0b01
* **Verification goals:** Ensure AxBURST == 0b01 is never false.

Cover the case where AxBURST == 0b01 is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** AXI Design doc - Address structure
* **Feature Description:** All Read transaction performed by CVA6 are of burst lenght less or equal to ICACHE_LINE_WIDTH/64. ARLEN = 0b01 or 0b00
* **Verification goals:** Ensure ARLEN == 0b01 || ARLEN == 0b00 is never false.

Cover the case where ARLEN == 0b01 || ARLEN == 0b00 is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P000_I001
* **Comments:** 

#### 002 item

* **Requirement location:** AXI Design doc - Address structure
* **Feature Description:** All write transaction performed by CVA6 are of burst lenght equal to 1. AWLEN = 0b00
* **Verification goals:** Ensure AWLEN == 0b00 is never false.

Cover the case where AWLEN == 0b00 is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P000_I002
* **Comments:** 

#### 003 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.4.1)
* **Feature Description:** The size of a read transfer does not exceed the width of the data interface. The maximum value can be taking by AxSIZE is 3.
* **Verification goals:** Check to ensure that AxSIZE is less or equal to log2(AXI_DATA_WIDTH/8)
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P000_I003
* **Comments:** 

#### 007 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A7.2.4)
* **Feature Description:** Exclusive access transactions cannot have a length greater than 16 beats
* **Verification goals:** Ensure AxLOCK && AxLEN > 15 is never true.

Cover the case where AxLOCK && AxLEN > 15 is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P000_I007
* **Comments:** 

#### 009 item

* **Requirement location:** 
* **Feature Description:** the write data is 1, 2, 4 or 8 bytes for AtomicLoad and AtomicSwap operations
* **Verification goals:** Check to ensure that the AWLEN * AWSIZE is equal to 1, 2, 4 or 8
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP005_P000_I009
* **Comments:** 

### 001_Dependency sub-feature

#### 001 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.4.1)
* **Feature Description:** The number of write data items matches AWLEN for the corresponding address
* **Verification goals:** Check to ensure that:
The Master assert the WLAST signal,  when the WDATA count is equal to AWLEN
The Master don't assert the WLAST, when the WDATA count is not equal to AWLEN
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P001_I001
* **Comments:** 

#### 002 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.4.4)
* **Feature Description:** Write strobes must only be asserted for the correct byte lanes
* **Verification goals:** Check to ensure that the strobe bits associated to the lanes that do not contain valid data are equal to zero.

For the other bits of the strob can take any value.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P001_I002
* **Comments:** 

#### 003 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.4.5)
* **Feature Description:** All write transaction addresses are matched with a corresponding buffered response
* **Verification goals:** check to ensure that after every write request a response handshake ocure in an unspecified delay with the same ID of the write request.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** ENV Capability
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P001_I003
* **Comments:** 

#### 004 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A7.2)
* **Feature Description:** An EXOKAY response can only be given to an exclusive access
* **Verification goals:** Check to ensure that an EXOKAY response occur only if there are an outstanding exclusive transaction with an ID that match the response ID
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P001_I004
* **Comments:** 

#### 005 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A5.2)
* **Feature Description:** The read data must always follow the address that it relates to.
* **Verification goals:** Check to ensure that a read data occur if there are an outstanding read transaction with an ID that match the the transaction request ID
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P001_I005
* **Comments:** 

#### 006 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.4.1)
* **Feature Description:** The number of read data items must match the corresponding ARLEN.
* **Verification goals:** Check to ensure that the subordinate assert the RLAST signal when it is driving the final read transfer in the burst

Check to ensure that the read burst not terminate early
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P001_I006
* **Comments:** 

#### 007 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.4.1)
* **Feature Description:** All outstanding read bursts must have completed.
* **Verification goals:** Check to ensure that the RLAST counter is equal to handshake counter.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP005_P001_I007
* **Comments:** 

#### 008 item

* **Requirement location:** 
* **Feature Description:** if an atomic operation has a burst length greater than one, AWSIZE is full data bus width
* **Verification goals:** Ensure that AWLEN > 0 &&  AWSIZE == AXI_DATA_WIDTH is always true

Cover the case where AWLEN > 0 &&  AWSIZE == AXI_DATA_WIDTH  is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP005_P001_I008
* **Comments:** 

#### 009 item

* **Requirement location:** 
* **Feature Description:** An atomic operation has an AWADDR is aligned to the data size for AtomicStore, AtomicLoad, and AtomicSwap
* **Verification goals:** Ensure that AWADDRE is always aligned to AWSIZE is always true
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP005_P001_I009
* **Comments:** 

#### 012 item

* **Requirement location:** 
* **Feature Description:** ID used to identify an Atomic transactions has not been used for other transactions that are outstanding at the same time
* **Verification goals:** 
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP005_P001_I012
* **Comments:** 

#### 013 item

* **Requirement location:** 
* **Feature Description:** For AtomicStore, AtomicLoad, and AtomicSwap, the write data is 1, 2, 4, or 8 bytes and read data is 1, 2, 4, or 8 bytes respectively.
* **Verification goals:** Check to ensure that read data that is not preceded by an outstanding read address with the same ID, have the same size as an outstanding transaction that have the same ID
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP005_P001_I013
* **Comments:** 

#### 015 item

* **Requirement location:** 
* **Feature Description:** For AtomicLoad, AtomicStore and AtomicSwap, the original data value at the addressed location is returned in read data channel
* **Verification goals:** Check to ensure that read data that is not preceded by an outstanding read address with the same ID, must be preceded by an outstanding atomic transaction that have the same ID
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP005_P001_I015
* **Comments:** 

## Signals feature

### 000_ID sub-feature

#### 000 item

* **Requirement location:** AXI Design doc - Transaction Identifiers
* **Feature Description:** The CVA6 identify read transaction with an ID equal to 0 or 1
* **Verification goals:** Ensure ARID == 0b01 || ARID == 0b00 is never false.

Cover the case where ARID == 0b01 || ARID == 0b00   is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP006_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** AXI Design doc - Transaction Identifiers
* **Feature Description:** The CVA6 identify write transaction with an ID equal to 1
* **Verification goals:** Ensure AWID == 0b01 is never false.

Cover the case where AWID == 0b01 is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP006_P000_I001
* **Comments:** 

#### 002 item

* **Requirement location:** AXI Design doc - Transaction Identifiers
* **Feature Description:** The CVA6 identify Atomic operation with an ID equal to 3
* **Verification goals:** Ensure AWID == 0b011 && Atomic_transaction is never false.

Cover the case where AWID == 0b011 && Atomic_transaction  is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP006_P000_I002
* **Comments:** 

### 001_User sub-feature

#### 000 item

* **Requirement location:** AXI Design doc - (table 2.2 and 2.5)
* **Feature Description:** User-defined extension for the write and read address channel is not supported. AxUSER = 0b00
* **Verification goals:** Ensure AxUSER = 0b00 is never false.

Cover the case where AxUSER = 0b00   is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP006_P001_I000
* **Comments:** 

#### 001 item

* **Requirement location:** AXI Design doc - (table 2.4)
* **Feature Description:** User-defined extension for the write response channel is not supported.
* **Verification goals:** Ensure BUSER = 0b00 is never false.

Cover the case where BUSER = 0b00   is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP006_P001_I001
* **Comments:** 

### 002_Quality_of_Service sub-feature

#### 000 item

* **Requirement location:** AXI Design doc - (table 2.2 and 2.5)
* **Feature Description:** Quality of Service identifier is not supported. AxQOS = 0b0000
* **Verification goals:** Ensure AxQOS = 0b0000 is never false.

Cover the case where AxQOS = 0b0000   is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP006_P002_I000
* **Comments:** 

### 003_Cache sub-feature

#### 000 item

* **Requirement location:** AXI Design Doc - Transaction Attributes: Memory types
* **Feature Description:** AxCACHE always take 0b0000.
* **Verification goals:** Ensure AxCACHE = 0b0000 is never false.

Cover the case where AxCACHE = 0b0000   is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP006_P003_I000
* **Comments:** 

### 004_Protection sub-feature

#### 000 item

* **Requirement location:** AXI Design Doc - (Table 2.2 and 2.5)
* **Feature Description:** Protection attributes always take the 0b000
* **Verification goals:** Ensure AxPROT = 0b000 is never false.

Cover the case where AxPROT = 0b000   is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP006_P004_I000
* **Comments:** 

### 006_Atomic_transaction sub-feature

#### 000 item

* **Requirement location:** AXI Design Doc - Atomic transactions
* **Feature Description:** CVA6 support just the AtomicLoad and AtomicSwap transaction. AWATOP[5:4] can be 00, 10 or 11
* **Verification goals:** Ensure AWATOP[5:4] = 0b00 || AWATOP[5:4] = 0b10 || AWATOP[5:4] = 0b11 is never false.

Cover the case where AWATOP[5:4] = 0b00 || AWATOP[5:4] = 0b10 || AWATOP[5:4] = 0b11   is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP006_P006_I000
* **Comments:** 

#### 001 item

* **Requirement location:** AXI Design Doc - Atomic transactions
* **Feature Description:** CVA6 perform only little-endian operation. AWATOP[3] = 0
* **Verification goals:** Ensure AWATOP[3] = 0b0 is never false.

Cover the case where AWATOP[3] = 0b0 is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP006_P006_I001
* **Comments:** 

### 007_Lock sub-feature

#### 000 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section E1.1.5)
* **Feature Description:** AWLOCK is 0 for Atomic operation
* **Verification goals:** Ensure that !AWLOCK && Atomic_operation is is always true

Cover the case where !AWLOCK && Atomic_operation is false
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP006_P007_I000
* **Comments:** 

### 008_Region sub-feature

#### 000 item

* **Requirement location:** AXI Design doc - (table 2.2 and 2.5)
* **Feature Description:** Region indicator is not supported. AxREGION = 0b0000
* **Verification goals:** Ensure AxREGION = 0b0000 is never false.

Cover the case where AxREGION = 0b0000   is false.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** Constrained Random
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP006_P008_I000
* **Comments:** 

## Clock and Reset feature

### 000_Signals_Value sub-feature

#### 000 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.1.2)
* **Feature Description:** A value of X on [Ax | x]VALID is not permitted when not in reset
* **Verification goals:** Ensure reset && [Ax | x]VALID == X is never true.

Cover the case where reset && [Ax | x]VALID == X is true.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** ENV Capability
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.1.2)
* **Feature Description:** A value of X on [Ax | x]READY is not permitted when not in reset
* **Verification goals:** Ensure reset && [Ax | x]READY == X is never true.

Cover the case where reset && [Ax | x]READY == X is true.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** ENV Capability
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P000_I001
* **Comments:** 

#### 002 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Figure A3-1)
* **Feature Description:** [Ax | x]VALID is LOW for the first cycle after RESET goes HIGH
* **Verification goals:** Ensure that [Ax | x]VALID is low the first cycle after RESET

Cover the case where [Ax | x]VALID is high the first cycle after RESET
* **Pass/Fail Criteria:** Assertion
* **Test Type:** ENV Capability
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP007_P000_I002
* **Comments:** 

## Handshake_Process feature

### 000_Stability  sub-feature

#### 000 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.2.2)
* **Feature Description:** All signals must remain stable when [Ax | x]VALID is asserted and [Ax | x]READY is LOW
* **Verification goals:** Check to ensure that all the signals does not change while [Ax | x]VALID is asserted.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** ENV Capability
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P000_I000
* **Comments:** 

#### 001 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.2.1)
* **Feature Description:** [Ax | x]VALID must remain asserted until [Ax | x]READY is HIGH
* **Verification goals:** Check to ensure that [Ax | x]VALID does not change while [Ax | x]READY is asserted.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** ENV Capability
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P000_I001
* **Comments:** 

### 001_Timing sub-feature

#### 000 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.3.1)
* **Feature Description:** The Manager must not wait for the Subordinate to assert ARREADY before asserting ARVALID
* **Verification goals:** Ensure that no errors are encountered as the testbench injects random Ready-to-Valid delays.  There are two cases to consider:  
                                                
ARREADY is asserted on or after same cycle as ARVALID
ARREADY is asserted and deasserted during an interval when ARVALID is de-asserted
* **Pass/Fail Criteria:** Any/All
* **Test Type:** ENV Capability
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P001_I000
* **Comments:** 

#### 001 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.3.1)
* **Feature Description:** The Subordinate must wait for both ARVALID and ARREADY to be asserted before it asserts RVALID to indicate that valid data is available.
* **Verification goals:** Check to ensure that every read data occur have the same ID to an outstanding read transaction.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P001_I001
* **Comments:** 

#### 002 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.3.1)
* **Feature Description:** The Manager must not wait for the Subordinate to assert AWREADY before asserting AWVALID or WVALID.
* **Verification goals:** Ensure that no errors are encountered as the testbench injects random Ready-to-Valid delays. There are two cases to consider:  
                                        
AWREADY is asserted on or after same cycle as AWVALID or WVALID
AWREADY is asserted and deasserted during an interval when AWVALID or WVALID is de-asserted
* **Pass/Fail Criteria:** Any/All
* **Test Type:** ENV Capability
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P001_I002
* **Comments:** 

#### 003 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.3.1)
* **Feature Description:** The Manager must not wait for the Subordinate to assert WREADY before asserting AWVALID or WVALID.
* **Verification goals:** Ensure that no errors are encountered as the testbench injects random Ready-to-Valid delays. There are two cases to consider:  
                                                
WREADY is asserted on or after same cycle as AWVALID or WVALID
WREADY is asserted and deasserted during an interval when AWVALID or WVALID is de-asserted
* **Pass/Fail Criteria:** Any/All
* **Test Type:** ENV Capability
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P001_I003
* **Comments:** 

#### 004 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.3.1)
* **Feature Description:** The Subordinate must wait for AWVALID, AWREADY, WVALID,  WREADY and also WLAST to be asserted before asserting BVALID
* **Verification goals:** Check to ensure that each response occur have the same ID as an outstanding write transaction that has been completed.
* **Pass/Fail Criteria:** Assertion
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** Assertion Coverage
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P001_I004
* **Comments:** 

#### 005 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A3.3.1)
* **Feature Description:** The Subordinate must not wait for the Manager to assert [B | R]READY before asserting [B | R]VALID
* **Verification goals:** No specific “observable checks” to be made in simulation. Testbench will always provide response data independently of [B | R]READY.
* **Pass/Fail Criteria:** Any/All
* **Test Type:** Other
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P001_I005
* **Comments:** 

#### 006 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section E1.1.9)
* **Feature Description:** On Atomic Operation, the Subordinate must wait for both AWVALID and AWREADY to be asserted before it asserts RVALID to indicate that valid data is available.
* **Verification goals:** No specific “observable checks” to be made in simulation. Testbench will always serve read data after the write address handshake.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP008_P001_I006
* **Comments:** 

#### 007 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section E1.1.9)
* **Feature Description:** On Atomic Operation, the Manager must not wait for the Subordinate to assert RVALID before asserting WVALID.
* **Verification goals:** Ensure that no errors are encountered as the testbench injects random valid write data.  There are three cases to consider:  
                                                
WVALID is asserted on ther same cycle as RVALID
WVALID is asserted after the cycle when RVALID is asserted
WVALID is asserted before the cycle when RVALID is asserted
* **Pass/Fail Criteria:** Any/All
* **Test Type:** ENV Capability
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6-step1, CV32A6-step2
* **Link to Coverage:** VP_IP008_P001_I007
* **Comments:** 

### 002_Ordering_Model sub-feature

#### 000 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A6.1)
* **Feature Description:** Transaction requests on the same channel, with the same ID and destination are guaranteed to remain in order.
* **Verification goals:** No specific “observable checks” to be made in simulation. The RM will check the data value and the xLAST assertion will ensure that the length of each transaction is respected
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P002_I000
* **Comments:** 

#### 001 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A6.1)
* **Feature Description:** Transaction responses with the same ID are returned in the same order as the requests were issued
* **Verification goals:** No specific “observable checks” to be made in simulation. The RM will check the data value and the Xlast assertion will ensure that the length of each transaction is respected.
* **Pass/Fail Criteria:** Check RM
* **Test Type:** Constrained Random
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P002_I001
* **Comments:** 

#### 002 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A6.1)
* **Feature Description:** If the CVA6 requires ordering between transactions that have no ordering guarantee, the Manager must wait to receive a response to the first transaction before issuing the second transaction.
* **Verification goals:** No specific “observable checks” to be made in simulation.
* **Pass/Fail Criteria:** NDY (Not Defined Yet)
* **Test Type:** NDY (Not Defined Yet)
* **Coverage Method:** NDY (Not Defined Yet)
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P002_I002
* **Comments:** 

#### 003 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A6.1)
* **Feature Description:** The READ and WRITE channels can have multiple outstanding transactions.
* **Verification goals:** Coverage of multiple outstanding transactions.
* **Pass/Fail Criteria:** Any/All
* **Test Type:** ENV Capability
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P002_I003
* **Comments:** 

#### 004 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A6.1)
* **Feature Description:** Transaction responses with the different ID can returne in any order.
* **Verification goals:** Ensure that no errors are encountered as the testbench injects read data transaction out of order.  There are two cases to consider:  

Two transaction, One with an ID equal to 0, the other with ID equal to 1
More than two transaction, we can have for each ID more than one transaction
* **Pass/Fail Criteria:** Check RM
* **Test Type:** ENV Capability
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P002_I004
* **Comments:** 

#### 005 item

* **Requirement location:** https://developer.arm.com/documentation/ihi0022/hc - (Section A6.1)
* **Feature Description:** CVA6 can accepte interleaved Read Data.
* **Verification goals:** Coverage of multiple interleaved Read Data.
* **Pass/Fail Criteria:** Any/All
* **Test Type:** ENV Capability
* **Coverage Method:** N/A
* **Applicable Cores:** CV32A6-step1, CV32A6-step2, CV64A6-step3
* **Link to Coverage:** VP_IP008_P002_I005
* **Comments:** 

