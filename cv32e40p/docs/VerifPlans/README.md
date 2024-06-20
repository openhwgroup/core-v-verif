<!--- SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0 --->
This is the root directory of the CV32E40P Verification Plan (aka Test Plan).  Each sub-directory is the Verification Plan a specific CV32E40P high-level feature of the same name.

Use the provided CORE-V_Simulation VerifPlan_Template.xlsx spreadsheet as your template to capture a Verification Plan.

Below are two different chapters describing verification plans status and direct link for CV32E40P**v2** verification plans first, and CV32E40P**v1** after.

# CV32E40P (V2) Verification Plans

## Short verification methodology introduction
For CV32E40P**v2** verification, the formal verification methodology has been choosen over the stimuli-based simulation that was done for version one of the core. However, full verification closure is not feasible using only formal verification due to complexity of specific scenarios. All these specific uncoverable scenarios from formal verification are then exercised by stimuli-based simulation using a reference model of the core. These scenarios along with formal assertions are described inside verifications plans, for which details are given in a table below. Regarding already available v1 plans, their re-use or not is specified in this table.

## Verification Plan Status

The tables below capture the current status of the Verification Plan for the CV32E40P by high-level feature, as long with status update with respect to CV32E40Pv1 verification plans.  Under the heading `VPlan Status`, the test plan can be **Incomplete**, **draft**. If the verification is **captured**, it has one of the following status:
* **v1-reused**: Vplan has been captured during v1 verification and has no modifications since then
* **v1-updated**: Vplan has been captured during v1 verification and contains updates, described in comments
* **v2-sim-new**: Vplan captures either new features or features not tested in v1 that will be execised within simulation environment
* **v2-formal-new**: Vplan captures either new features or features not tested in v1 that are verified using formal

Under the heading `Review Status` is one of following:
* **Not Available for Review**: Vplan has been captured, but is not available for review yet
* **Ready for Review**: Vplan has been captured and is awaiting review.
* **Reviewed**: Vplan has been reviewed, and is waiting for updates to address review feedback.
* **Waiting for Signoff**: Vplan has been reviewed and review comments addressed by the author.  Document is now waiting for reviewers to signoff on the post-review updates.
* **Complete**: Post-preview updates have been signed-off.

Under the heading `Link`, the name shown corresponds to the filename of the vplan. The hyperlink is a direct link to the latest up-to-date version of the verification plan.

| Category            | Feature        | VPlan Status | Review Status | Comment | Link |
|---------------------|----------------|--------------|---------------|---------|------|
| **Base Instruction Set** | RV32IMC + F + Zfinx + Zifencei | v2-formal-new | Reviewed |      | [CV32E40Pv2_Formal_VerificationPlans.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/RISC-V_ISA_Formal/CV32E40Pv2_Formal_VerificationPlans.xlsx) |
| **Interrupts**      | CLINT | v1-updated   | Reviewed | Addition of missing XPULP / F / Zfinx interrupts | [CV32E40P_interrupts.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/Simulation/interrupts/CV32E40Pv2_interrupts.xlsx "Interrupts Vplan")|
| **Debug & Trace**   | Debug          | v1-reused | Reviewed | Missing XPULP-specific debug are in a separate vplan | [CV32E40P_debug.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/Simulation/debug-trace/CV32E40Pv2_debug.xlsx "Debug Vplan")|
| **Privileged Spec** | CSRs / Zicsr | v2-formal-new | Reviewed | [CV32E40Pv2_Formal_VerificationPlans.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/RISC-V_ISA_Formal/CV32E40Pv2_Formal_VerificationPlans.xlsx) |      |
| **Micro-architecture** | OBI |  v1-reused  | Reviewed |         | [CV32E40P_OBI_VerifPlan.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/Simulation/micro_architecture/CV32E40P_OBI_VerifPlan.xlsx "OBI Vplan") |
|                        | Pipeline / SleepUnit | v1-reused | Reviewed |  | [CV32E40P_Pipeline_Sleep.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/Simulation/micro_architecture/CV32E40P_Pipeline_Sleep.xlsx "Pipeline Sleep Vplan") |
|                        | FPU Register File | v2-sim-new | Reviewed |  | [CV32E40P_FPU_register_file.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/Simulation/micro_architecture/CV32E40Pv2_FPU_register_file.xlsx "FPU Reg. File Vplan") |
| **Additional ISA** | F / Zfinx | v2-sim-new | Reviewed | Includes uncoverable items from formal verification | [CV32E40P_F-Zfinx-instructions.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/Simulation/Zfinx_F_instructions/CV32E40Pv2_F-Zfinx-instructions.xlsx "Add. F/Zfinx Vplan") |
| **XPULP** | Post-Increment Load/Store (Formal) | v2-formal-new | Reviewed | [CV32E40Pv2_Formal_VerificationPlans.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/RISC-V_ISA_Formal/CV32E40Pv2_Formal_VerificationPlans.xlsx) |
|  | Post-Increment Load/Store (Simulation) | v2-sim-new | Reviewed | Addition of "pipeline" with simulation (preceeding F multicycle)  | [CV32E40P_xpulp-postinc-loadstore.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40Pv2_xpulp-postinc-loadstore.xlsx "Post-Inc Load/Store simu Vplan") |
|  | Bitmanipulation (Formal) | v2-formal-new | Reviewed |      | [CV32E40Pv2_Formal_VerificationPlans.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/RISC-V_ISA_Formal/CV32E40Pv2_Formal_VerificationPlans.xlsx) |
|  | Bitmanipulation (Simulation) | v2-sim-new | Reviewed | Lowest priority as formal already checks everything needed, added because corev-dv generator will generate those instructions anyway  | [CV32E40P_xpulp-bitmanipulation.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40Pv2_xpulp-bitmanipulations.xlsx "Bitmanip simu Vplan") |
|  | General ALU (Formal) | v2-formal-new | Reviewed |      | [CV32E40Pv2_Formal_VerificationPlans.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/RISC-V_ISA_Formal/CV32E40Pv2_Formal_VerificationPlans.xlsx) |
|  | General ALU (Simulation) | v2-simu-new | Reviewed | Lowest priority as formal already checks everything needed, added because corev-dv generator will generate those instructions anyway  | [CV32E40P_xpulp-general-alu.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40Pv2_xpulp-general-alu.xlsx "General ALU simu Vplan") |
|  | Immediate Branching (Formal) | v2-formal-new | Reviewed |      | [CV32E40Pv2_Formal_VerificationPlans.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/RISC-V_ISA_Formal/CV32E40Pv2_Formal_VerificationPlans.xlsx) |
|  | Immediate Branching (Simulation) | v2-simu-new | Reviewed | Lowest priority as formal already checks everything needed, added because corev-dv generator will generate those instructions anyway  | [CV32E40P_xpulp-immediate-branching.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40Pv2_xpulp-immediate-branching.xlsx "Imm Branching simu Vplan") |
|  | MAC (Formal) | v2-formal-new | Reviewed |      | [CV32E40Pv2_Formal_VerificationPlans.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/RISC-V_ISA_Formal/CV32E40Pv2_Formal_VerificationPlans.xlsx) |
|  | MAC (Simulation) | v2-sim-new | Reviewed | Addition of missing coverage from formal (operands "toggle")   | [CV32E40P_xpulp-multiply-accumulate.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40Pv2_xpulp-multiply-accumulate.xlsx "MAC simu Vplan") |
|  | SIMD (Formal) | v2-formal-new | Reviewed |      | [CV32E40Pv2_Formal_VerificationPlans.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/RISC-V_ISA_Formal/CV32E40Pv2_Formal_VerificationPlans.xlsx) |
|  | SIMD (Simulation) | v2-sim-new | Reviewed | Addition of missing coverage from formal (operands "toggle")   | [CV32E40P_xpulp-packed-simd.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40Pv2_xpulp-packed-simd.xlsx "SIMD simu Vplan") |
|  | HWLoop (Simulation) | v2-sim-new | Reviewed | Feature not test at all in formal verification | [CV32E40P_xpulp-hwloop.xlsx](https://github.com/openhwgroup/core-v-verif/blob/cv32e40p/dev/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40Pv2_xpulp-hwloop.xlsx "HWLoop Vplan") |


</br>
</br>
</br>

________________________________________________________________________

# CV32E40P (V1) Verification Plans

Below are the verification plans status for the first version of the core.

## Verification Plan Status

The tables below capture the current status of the Verification Plan for the CV32E40P by high-level feature.  Under the heading `Review Status` is one of following:
* **Ready for Review**: Vplan has been captured and is awaiting review.
* **Reviewed**: Vplan has been reviewed, and is waiting for updates to address review feedback.
* **Waiting for Signoff**: Vplan has been reviewed and review comments addressed by the author.  Document is now waiting for reviewers to signoff on the post-review updates.
* **Complete**: Post-preview updates have been signed-off.

### Base instruction set plus standard instruction extensions

_Refer to the [VerifPlans/ISA/RV32/Simulation](https://github.com/openhwgroup/core-v-verif/tree/4bb9858cd7c58f8856ff544f53fe102c76ea9683/docs/VerifPlans/ISA/RV32/Simulation "ISA Simulation vPlans") directory for specific Verification Plan status for each supported extension._
### Interrupts

| Feature        | VPlan Status | Review Status | Comment | Link |
|----------------|--------------|---------------|---------|------|
| CLINT | Captured | Complete | | [CV32E40P_interrupts.xlsx](https://github.com/openhwgroup/core-v-verif/blob/4bb9858cd7c58f8856ff544f53fe102c76ea9683/cv32e40p/docs/VerifPlans/Simulation/interrupts/CV32E40P_interrupts.xlsx "v1 Interrupts Vplan") |
| CLIC | | | Not a CV32E40P Feature | |

### Debug & Trace

| Feature        | VPlan Status | Review Status | Comment | Link |
|----------------|--------------|---------------|---------|------|
| Debug | Captured | Complete | | [CV32E40P_debug.xlsx](https://github.com/openhwgroup/core-v-verif/blob/4bb9858cd7c58f8856ff544f53fe102c76ea9683/cv32e40p/docs/VerifPlans/Simulation/debug-trace/CV32E40P_debug.xlsx "Debug Vplan") |
| Trigger module | Captured | Complete | Not a CV32E40P Feature | |
| Tracer | N/A | N/A | Behavioral model, not RTL | |

### Privileged spec

| Feature        | VPlan Status | Review Status | Comment | Link |
|----------------|--------------|---------------|---------|------|
| CSRs | Incomplete | | | [CSR_Vplan.md](https://github.com/openhwgroup/core-v-verif/blob/4bb9858cd7c58f8856ff544f53fe102c76ea9683/cv32e40p/docs/VerifPlans/Simulation/privileged_spec/CSR_Vplan.md "v1 CSR Vplan") |
| User mode | N/A| N/A | Not a CV32E40P Feature | |
| PMP | N/A | N/A | Not a CV32E40P Feature | |

### Micro-architecure

| Feature        | VPlan Status | Review Status | Comment | Link |
|----------------|--------------|---------------|---------|------|
| OBI     | Complete | Reviewed | | [CV32E40P_OBI_VerifPlan.xlsx](https://github.com/openhwgroup/core-v-verif/blob/4bb9858cd7c58f8856ff544f53fe102c76ea9683/cv32e40p/docs/VerifPlans/Simulation/micro_architecture/CV32E40P_OBI_VerifPlan.xlsx "v1 OBI Vplan") |
| Sleep Unit | Complete | Reviewed | Updates pending based on review feedback | [CV32E40P_Pipeline_Sleep.xlsx](https://github.com/openhwgroup/core-v-verif/blob/4bb9858cd7c58f8856ff544f53fe102c76ea9683/cv32e40p/docs/VerifPlans/Simulation/micro_architecture/CV32E40P_Pipeline_Sleep.xlsx "v1 Pipeline Sleep Vplan") |
| Pipelines | Complete | Reviewed | Updates pending based on review feedback | [CV32E40P_Pipeline_Sleep.xlsx](https://github.com/openhwgroup/core-v-verif/blob/4bb9858cd7c58f8856ff544f53fe102c76ea9683/cv32e40p/docs/VerifPlans/Simulation/micro_architecture/CV32E40P_Pipeline_Sleep.xlsx "v1 Pipeline Sleep Vplan") |

### Xpulp instruction extensions
**Note**: Xpulp instructions are "exercised, but not fully verified" in CV32E40P.

| Feature        | VPlan Status | Review Status | Comment | Link |
|----------------|--------------|---------------|---------|------|
| Post-increment load/store | Preliminary draft | | | [CV32E40P_xpulp-postinc-loadstore.xlsx](https://github.com/openhwgroup/core-v-verif/blob/4bb9858cd7c58f8856ff544f53fe102c76ea9683/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40P_xpulp-postinc-loadstore.xlsx "v1 Post-Inc Load/Store simu Vplan") | |
| Hardware Loop | Preliminary draft | | On-going discussions with Cores TWG | [CV32E40P_xpulp-hwloop.xlsx](https://github.com/openhwgroup/core-v-verif/blob/4bb9858cd7c58f8856ff544f53fe102c76ea9683/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40P_xpulp-hwloop.xlsx "v1 HWLoop Vplan") |
| Bit Manipulation | Preliminary draft | | | [CV32E40P_xpulp-bitmanipulation.xlsx](https://github.com/openhwgroup/core-v-verif/blob/4bb9858cd7c58f8856ff544f53fe102c76ea9683/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40P_xpulp-bitmanipulations.xlsx "v1 Bitmanip simu Vplan") |
| General ALU | Preliminary draft | | | [CV32E40P_xpulp-general-alu.xlsx](https://github.com/openhwgroup/core-v-verif/blob/4bb9858cd7c58f8856ff544f53fe102c76ea9683/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40P_xpulp-general-alu.xlsx "v1 General ALU simu Vplan") |
| Immediate branching | Preliminary draft | | | [CV32E40P_xpulp-immediate-branching.xlsx](https://github.com/openhwgroup/core-v-verif/blob/4bb9858cd7c58f8856ff544f53fe102c76ea9683/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40P_xpulp-immediate-branching.xlsx "v1 Imm Branching simu Vplan") |
| SIMD | Preliminary draft | | | [CV32E40P_xpulp-packed-simd.xlsx](https://github.com/openhwgroup/core-v-verif/blob/4bb9858cd7c58f8856ff544f53fe102c76ea9683/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40P_xpulp-packed-simd.xlsx "v1 SIMD simu Vplan") |
| MAC | Preliminary draft | | | [CV32E40P_xpulp-multiply-accumulate.xlsx](https://github.com/openhwgroup/core-v-verif/blob/4bb9858cd7c58f8856ff544f53fe102c76ea9683/cv32e40p/docs/VerifPlans/Simulation/xpulp_instruction_extensions/CV32E40P_xpulp-multiply-accumulate.xlsx "v1 MAC simu Vplan") |


### Custom circuitry

| Feature        | VPlan Status | Review Status | Comment | Link |
|----------------|--------------|---------------|---------|------|
| RI5CY performance counters | | | Not a CV32E40P Feature | |
| Advanced Processing Unit itf | | | Not a CV32E40P Feature | |
| 128-bit wide Instruction Bus itf | | | Not a CV32E40P Feature | |
| RI5CY interrupt scheme | | | Not a CV32E40P Feature | |
| PULP cluster itf | | | Not a CV32E40P Feature | |
