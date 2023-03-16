<!--- SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0 ---> 
This is the root directory of the CV32E40P Verification Plan (aka Test Plan).  Each sub-directory is the Verification Plan a specific CV32E40P high-level feature of the same name.

Use the provided CORE-V_Simulation VerifPlan_Template.xlsx spreadsheet as your template to capture a Verification Plan.

## Verification Plan Status

The tables below capture the current status of the Verification Plan for the CV32E40P by high-level feature, as long with status update with respect to CV32E40Pv1 verification plans.  Under the heading `Capture`, the test plan can be **Incomplete**, **draft**, or one of the following: 
* **Captured _(v1)_**: Vplan has been captured during v1 verification and has no modifications since then. 
* **Captured _(new)_**: Vplan captures either new features or features not tested in v1
* **Captured _(new method)_**: Vplan captures a different methodology from v1
* **Captured _(updated)_**: Vplan has been captured in v1, but contains modifications for v2

Under the heading `Review` is one of following:
* **Waiting for Review**: Vplan has been captured, but is not available for review yet
* **Ready for Review**: Vplan has been captured and is awaiting review.
* **Reviewed**: Vplan has been reviewed, and is waiting for updates to address review feedback.
* **Waiting for Signoff**: Vplan has been reviewed and review comments addressed by the author.  Document is now waiting for reviewers to signoff on the post-review updates.
* **Complete**: Post-preview updates have been signed-off.

### Base instruction set plus standard instruction extensions

Base instruction set plus standard instructions extensions have been mainly verified using formal tools for v2. Please refer to the documents inside `Formal` directory to have more details about assertions and properties used. 
The v1 _simulation_ verification plans can be found there: `core-v-verif/VerifPlans/ISA/RV32/Simulation`

### Interrupts

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| CLINT | Captured (**updated**) | Ready for Review | |
| CLIC | N/A | N/A | Not a CV32E40P Feature |

### Debug & Trace

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| Debug | Captured  (**updated**) | Ready for Review | |
| Trigger module | Captured (v1) | Complete | Not a CV32E40P Feature |
| Tracer | N/A | N/A | Behavioral model, not RTL |

### Privileged spec

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| CSRs | Captured (**new method**) | Waiting for Review | Verified by formal |
| User mode | N/A| N/A | Not a CV32E40P Feature |
| PMP | N/A | N/A | Not a CV32E40P Feature |

### Micro-architecure

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| OBI     | Captured (v1) | Reviewed | |
| Sleep Unit | Complete (v1) | Reviewed | Updates pending based on review feedback |
| Pipelines | Complete (v1) | Reviewed | Updates pending based on review feedback|
| FPU File Register | Complete (**new**) | Ready for Review | |

### F and Zfinx extensions
**Note**: As verifying all floating points instructions using formal tools **only** is too complex and would have required too much processing power, the missing features of F/Zfinx extension have been verified by simulation. 

| Features | Capture | Review | Comment |
|---------|---------|--------|---------|
| DIV and SQRT Instructions | Captured (**new**) | Ready for Review | Not covered at all by formal verification |
| FMUL/FDIV | Captured (**new**) | Ready for Review | Formal coverage issue: some bits of operands have been tied low | 
| FNMADD/FMADD | Captured (**new**) | Ready for Review | Formal coverage issue: some bits of operands have been tied low | 
| FNMSUB/FMSUB | Captured (**new**) | Ready for Review | Formal coverage issue: some bits of operands have been tied low |
| Other F instructions | Captured (**new**) | Ready for Review | Formal pipeline issue: Add preceeding F multicycle instruction |

### Xpulp instruction extensions
**Note**: Xpulp instructions are "exercised, but not fully verified" in CV32E40P.

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| Post-increment load/store | Captured (**new method**) | Waiting for Review | |
| Hardware Loop | Captured (**new**) | Ready for Review | |
| Bit Manipulation | Captured (**new method**) | Waiting for Review | |
| General ALU | Captured (**new method**) | Waiting for Review | |
| Immediate branching | Captured (**new method**) | Waiting for Review | |
| SIMD | Captured (**new method**) | Waiting for Review | |
| MAC | Captured (**new method**) | Waiting for Review | |

### Custom circuitry

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| RI5CY performance counters | | | Not a CV32E40P Feature |
| Advanced Processing Unit itf | | | Not a CV32E40P Feature |
| 128-bit wide Instruction Bus itf | | | Not a CV32E40P Feature |
| RI5CY interrupt scheme | | | Not a CV32E40P Feature |
| PULP cluster itf | | | Not a CV32E40P Feature |
