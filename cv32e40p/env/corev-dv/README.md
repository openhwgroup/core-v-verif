## Corev-dv
This directory contains core-v-verif extensions to [riscv-dv](https://github.com/google/riscv-dv).   The cloned code from Google is not locally
modified, and as much as is possible we attempt to use the latest-and-greatest from Google.  Any core-v-verif
specializations are implemented as either replacements (e.g the manifest) or extensions of specific SV classes.
<br><br>
Compile logs, runtime logs and the generated programs are placed here in the same `out_<YYYY_MM_DD>` directory used by riscv-dv.
<br>
<!-- TODO: re-direct the generated assembly language tests-programs to a central location. -->
<br><br>
The UVM environments in core-v-verif do not use the `run.py` python script to run the generator (although no changes are
made preventing _you_ from doing so).  Look for the `gen_corev-dv` target in the simulator-specific makefiles in `$CORE_V_VERIF/mk/uvmt/`
for an example of how core-v-verif runs the generator.
<br><br>

## Extensions to Riscv-dv specific to cv32e40p
Common extensions are detailed in the top level `core-v-verif/lib/corev-dv/README.md`

--------------------------------------------------------------------------------

#### cv32e40p\_asm\_program\_gen
Description:<br>
Implements support for cv32e40p fast interrupt handler.

| Extends                 |
|:------------------------|
| `corev_asm_program_gen` |

| Implements                      | Purpose |
|:--------------------------------|:--------|
| `init_gpr`                      | Skips initialization of dp if a debug section is generated |
| `gen_stack_section`             | Adds debugger stack sections to assembly file output |
| `gen_interrupt_handler_section` | Removes MIP read, since interrupts are auto-cleared, thus MIP will not track through ISS |
| `setup_epc`                     | Only difference from upstream is using the text-representation "mepc" rather than the numeric value 0x341 <!-- (TODO: Why do we need this change? Apparently this function can be removed from our overrides without any impact) --> |
| `gen_interrupt_vector_table`    | Modifies interrupt vector table generation to fetch corev configuration and selectively enable fast interrupt handlers based on corev-configuration. Configuration can also enable/disable insertion of wfi in the interrupt handlers. |

--------------------------------------------------------------------------------

#### cv32e40p\_debug\_rom\_gen
Description:<br>
Enables core-v-verif custom debug rom, with config fetched from corev configuration object.

| Extends               |
|:----------------------|
| `riscv_debug_rom_gen` |

| Implements                    | Purpose |
|:------------------------------|:--------|
| `gen_program`                 | Adds .debugger symbols to program |
|                               | Fetches corev-configuration |
|                               | Randomly inserts wfi at start of debug rom |
| `gen_debug_exception_handler` | Inserts debug section into assembly file |

--------------------------------------------------------------------------------

#### cv32e40p\_illegal\_instr
Description:<br>
Constrains illegal instruction generation from treating debug registers as non-implemented CSRs

| Extends               |
|:----------------------|
| `riscv_illegal_instr` |

| Implements                 | Purpose |
|:---------------------------|:--------|
| `missing_csr_debug_regs_c` | Adds debug CSRs to list of valid registers to consider when generating illegal instructions  |

--------------------------------------------------------------------------------

#### cv32e40p\_instr\_base\_test
Description:<br>
Enables class-wide overrides

| Extends                 |
|:------------------------|
| `corev_instr_base_test` |

| Implements    | Purpose |
|:--------------|:--------|
| `build_phase` | Enables overrides for the following: |
|               | `asm_program_gen` |
|               | `gen_config` |
|               | `compressed_instr` |
|               | `illegal_instr` |
|               | `privil_reg` |
|               | `privil_seq` |
|               | `debug_rom_gen` |

--------------------------------------------------------------------------------

#### cv32e40p\_instr\_gen\_config
Description:<br>
Enables support for cv32e40p fast interrupt handlers and constrains mtvec to be properly aligned
Adds debug pointer to reserved registers and disallows certain combinations of debug plusargs.

| Extends                  |
|:-------------------------|
| `riscv_instr_gen_config` |

| Implements                   | Purpose |
|:-----------------------------|:--------|
| `dp_c`                       | debug pointer constraint - not ra, sp or tp |
| `mtvec_c`                    | 256KB aligned mtvec |
| `knob_zero_fast_intr_dist_c` | 80% likely disabled, 20% likely enabled |
| `fast_intr_handler_c`        | enable `knob_zero_fast_intr_handlers` if fast handlers are disabled |
| `post_randomize`             | adds dp to reserved regs, disallow some debug ROM combinations using same register |

--------------------------------------------------------------------------------

#### cv32e40p\_instr\_test\_pkg

Description:<br>
Includes riscv-dv class override definitions and implements debug stack push/pop functions.

| Implements                    | Purpose |
|:------------------------------|:--------|
| `push_gpr_to_debugger_stack`  | Pushes all GPRs to debug stack |
| `pop_gpr_from_debugger_stack` | Pops all GPRs from debug stack|

--------------------------------------------------------------------------------

#### cv32e40p\_privil\_reg

Description:<br>
Adds register definitions for MIE and MIP

| Implements | Purpose |
|:-----------|:--------|
| `init_reg` | Adds MIE and MIP register fields relevant for 40p |

--------------------------------------------------------------------------------

#### cv32e40p\_csr\_template.yaml

Description:<br>
CSR definitions used for generating the csr test, see file header for details on usage.

--------------------------------------------------------------------------------
#### cv32e40p\_C\_LUI\_instr
<!-- TODO: Remove this section when this fix has been upstreamed. -->

Description:
This class is a bugfix for upstream riscv-dv. Compilers and Riscv ISA does not necessarily
implement offsets in the same manner. Negative integer offsets, which riscv-dv uses
extensively are not supported. To work around this, the negative offsets are expressed
as unsigned hex-values (0xffff...) instead.

| Extends             |
|:--------------------|
| `riscv_C_LUI_instr` |


| Implements       | Purpose |
|:-----------------|:--------|
| `imm_val_c`      | Avoids negative sign extension on offset value. |
| `extend_imm`     | Extends and masks offset. |
| `update_imm_str` | Encodes the offset as a 20-bit unsigned offset value. |


<!--
--------------------------------------------------------------------------------
TODO Fix Upstreamed to riscv dv - this extension should no longer be needed
if hash is updated
--------------------------------------------------------------------------------
#### cv32e40p\_privileged\_common\_seq
extends:
riscv\_privileged\_common\_seq
overrides/adds:
setup\_mmode\_reg:
Fix for riscv-dv bug 
--------------------------------------------------------------------------------
TODO END
--------------------------------------------------------------------------------
-->
