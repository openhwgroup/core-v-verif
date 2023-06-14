<!--- SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0 --->
This is the root directory of the CV32E40P Verification Plan (aka Test Plan).  Each sub-directory is the Verification Plan a specific CV32E40P high-level feature of the same name.

Use the provided CORE-V_Simulation VerifPlan_Template.xlsx spreadsheet as your template to capture a Verification Plan.

Below are two different chapters describing verification plans status and direct link for CV32E40P**v2** verification plans first, and CV32E40P**v1** after.

# CV32E40P (V2) Verification Plans

## Short verification methodology introduction
For CV32E40P**v2** verification, the formal verification methodology has been choosen over the stimuli-based simulation that was done for version one of the core. However, full verification closure is not feasible using only formal verification due to complexity of specific scenarios. All these specific uncoverable scenarios from formal verification are then exercised by stimuli-based simulation using a reference model of the core. These scenarios along with formal assertions are described inside verifications plans, for which details are given below. Regarding already available v1 plans, their re-use status is described in table

## Verification Plan Status

The tables below capture the current status of the Verification Plan for the CV32E40P by high-level feature, as long with status update with respect to CV32E40Pv1 verification plans.  Under the heading `Capture`, the test plan can be **Incomplete**, **draft**. If the verification is **captured**, it has one of the following status:
* **v1-reused**: Vplan has been captured during v1 verification and has no modifications since then
* **v1-updated**: Vplan has been captured during v1 verification and contains updates, described in comments
* **v2-sim-new**: Vplan captures either new features or features not tested in v1 that will be execised within simulation environment
* **v2-formal-new**: Vplan captures either new features or features not tested in v1 that are verified using formal

Under the heading `Review` is one of following:
* **Not Available for Review**: Vplan has been captured, but is not available for review yet
* **Ready for Review**: Vplan has been captured and is awaiting review.
* **Reviewed**: Vplan has been reviewed, and is waiting for updates to address review feedback.
* **Waiting for Signoff**: Vplan has been reviewed and review comments addressed by the author.  Document is now waiting for reviewers to signoff on the post-review updates.
* **Complete**: Post-preview updates have been signed-off.

Under the heading `Link`, the name shown corresponds to the filename of the vplan. The hyperlink is a direct link to the latest up-to-date version of the verification plan.

| Category            | Feature        | VPlan Status | Review Status | Comment | Link |
|---------------------|----------------|--------------|---------------|---------|------|
| **Base Instruction Set** | RV32IMC + F + Zfinx + Zifencei | v2-formal-new | Not Available for Review | Waiting Approval from Siemens |      |
| **Interrupts**      | CLINT | v1-updated   | **Ready for Review** | Addition of missing XPULP / F / Zfinx interrupts |[CV32E40P_interrupts.xlsx](https://github.com/openhwgroup/core-v-verif/blob/2378099bfce1c7b2b3d089ea2cb60ad422c05e94/cv32e40p/docs/VerifPlans/Simulation/interrupts/CV32E40P_interrupts.xlsx "Interrupts Vplan")|
| **Debug & Trace**   | Debug          | v1-reused | Reviewed | Need to be completed with XPULP-specific debug  |[CV32E40P_debug.xlsx](https://github.com/openhwgroup/core-v-verif/blob/2378099bfce1c7b2b3d089ea2cb60ad422c05e94/cv32e40p/docs/VerifPlans/Simulation/debug-trace/CV32E40P_debug.xlsx "Debug Vplan")|
| **Privileged Spec** | CSRs / Zicsr | v2-formal-new | Not Available for Review | Waiting Approval from Siemens |      |
| **Micro-architecture** | OBI |  v1-reused  | Reviewed |         | [CV32E40P_OBI_VerifPlan.xlsx](https://github.com/openhwgroup/core-v-verif/blob/2378099bfce1c7b2b3d089ea2cb60ad422c05e94/cv32e40p/docs/VerifPlans/Simulation/micro_architecture/CV32E40P_OBI_VerifPlan.xlsx "OBI Vplan") |
|                        | Pipeline / SleepUnit | v1-reused | Reviewed |  | [CV32E40P_Pipeline_Sleep.xlsx](https://github.com/openhwgroup/core-v-verif/blob/2378099bfce1c7b2b3d089ea2cb60ad422c05e94/cv32e40p/docs/VerifPlans/Simulation/micro_architecture/CV32E40P_Pipeline_Sleep.xlsx "Pipeline Sleep Vplan") |
|                        | FPU Register File | v2-sim-new | **Ready for Review** |  | [CV32E40P_FPU_register_file.xlsx](https://github.com/openhwgroup/core-v-verif/blob/2378099bfce1c7b2b3d089ea2cb60ad422c05e94/cv32e40p/docs/VerifPlans/Simulation/micro_architecture/CV32E40P_FPU_register_file.xlsx "FPU Reg. File Vplan") |
| **Additional ISA** | F / Zfinx | v2-sim-new | **Ready for Review** | Includes uncoverable items from formal verification | [CV32E40P_F-Zfinx-instructions.xlsx](https://github.com/openhwgroup/core-v-verif/blob/2378099bfce1c7b2b3d089ea2cb60ad422c05e94/cv32e40p/docs/VerifPlans/Simulation/Zfinx_F_instructions/CV32E40P_F-Zfinx-instructions.xlsx "Add. F/Zfinx Vplan") |
| **XPULP** | Post-Increment Load/Store (Formal) | v2-formal-new | Not Available for Review | Waiting Approval from Siemens |
|  | Post-Increment Load/Store (Simulation) | v2-sim-new | **Ready for Review** | "pipeline" with simulation (preceeding F multicycle)  | [CV32E40P_xpulp-postinc-loadstore.xlsx](https://github.com/openhwgroup/core-v-verif/blob/2378099bfce1c7b2b3d089ea2cb60ad422c05e94/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40P_xpulp-postinc-loadstore.xlsx "Post-Inc Load/Store simu Vplan") |
|  | Bitmanipulation (Formal) | v2-formal-new | Not Available for Review | Waiting Approval from Siemens | |
|  | General ALU (Formal) | v2-formal-new | Not Available for Review | Waiting Approval from Siemens | |
|  | Immediate Branching (Formal) | v2-formal-new | Not Available for Review | Waiting Approval from Siemens | |
|  | MAC (Formal) | v2-formal-new | Not Available for Review | Waiting Approval from Siemens |
|  | MAC (Simulation) | v2-sim-new | **Ready for Review** | missing coverage from formal ("toggle")   | [CV32E40P_xpulp-multiply-accumulate.xlsx](https://github.com/openhwgroup/core-v-verif/blob/2378099bfce1c7b2b3d089ea2cb60ad422c05e94/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40P_xpulp-multiply-accumulate.xlsx "MAC simu Vplan") |
|  | SIMD (Formal) | v2-formal-new | Not Available for Review | Waiting Approval from Siemens |
|  | SIMD (Simulation) | v2-sim-new | **Ready for Review** | missing coverage from formal ("toggle")   | [CV32E40P_xpulp-packed-simd.xlsx](https://github.com/openhwgroup/core-v-verif/blob/2378099bfce1c7b2b3d089ea2cb60ad422c05e94/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40P_xpulp-packed-simd.xlsx "SIMD simu Vplan") |
|  | HWLoop (Simulation) | v2-sim-new | **Ready for Review** | Feature not test at all in formal verification | [CV32E40P_xpulp-hwloop.xlsx](https://github.com/openhwgroup/core-v-verif/blob/2378099bfce1c7b2b3d089ea2cb60ad422c05e94/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40P_xpulp-hwloop.xlsx "HWLoop Vplan") |



# CV32E40P (V1) Verification Plans
## Verification Plan Status

The tables below capture the current status of the Verification Plan for the CV32E40P by high-level feature.  Under the heading `Review` is one of following:
* **Ready for Review**: Vplan has been captured and is awaiting review.
* **Reviewed**: Vplan has been reviewed, and is waiting for updates to address review feedback.
* **Waiting for Signoff**: Vplan has been reviewed and review comments addressed by the author.  Document is now waiting for reviewers to signoff on the post-review updates.
* **Complete**: Post-preview updates have been signed-off.

### Base instruction set plus standard instruction extensions

_Refer to the VerifPlans/ISA/RV32/Simulation directory for specific Verification Plan status for each supported extension._
### Interrupts

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| CLINT | Captured | Complete | |
| CLIC | | | Not a CV32E40P Feature |

### Debug & Trace

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| Debug | Captured | Complete | |
| Trigger module | Captured | Complete | Not a CV32E40P Feature |
| Tracer | N/A | N/A | Behavioral model, not RTL |

### Privileged spec

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| CSRs | Incomplete | | |
| User mode | N/A| N/A | Not a CV32E40P Feature |
| PMP | N/A | N/A | Not a CV32E40P Feature |

### Micro-architecure

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| OBI     | Complete | Reviewed | |
| Sleep Unit | Complete | Reviewed | Updates pending based on review feedback |
| Pipelines | Complete | Reviewed | Updates pending based on review feedback|

### Xpulp instruction extensions
**Note**: Xpulp instructions are "exercised, but not fully verified" in CV32E40P.

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| Post-increment load/store | Preliminary draft | | |
| Hardware Loop | Preliminary draft | | On-going discussions with Cores TWG |
| Bit Manipulation | Preliminary draft | | |
| General ALU | Preliminary draft | | |
| Immediate branching | Preliminary draft | | |
| SIMD | Preliminary draft | | |

### Custom circuitry

| Feature | Capture | Review | Comment |
|---------|---------|--------|---------|
| RI5CY performance counters | | | Not a CV32E40P Feature |
| Advanced Processing Unit itf | | | Not a CV32E40P Feature |
| 128-bit wide Instruction Bus itf | | | Not a CV32E40P Feature |
| RI5CY interrupt scheme | | | Not a CV32E40P Feature |
| PULP cluster itf | | | Not a CV32E40P Feature |
