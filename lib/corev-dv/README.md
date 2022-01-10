## corev-dv
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

## Common extensions to Riscv-dv
The following sections describe common class extensions to riscv-dv that are created for core-v-verif, methods only implementing .super are omitted for brevity.

--------------------------------------------------------------------------------

#### corev\_asm\_program\_gen

Description:<br>
Main assembly generation routine.
- Creates program header suitable for the core-v-verif environment.
  - Main difference from `riscv_asm_program_gen` is the addition of mtvec symbols, and removed support for multiple harts.
- Sets up "Done" test printout and sets status register states upon completion.
- Overrides ecall-handler override to facilitate ECALL-tests, as riscv-dv implementation terminates test when an ECALL is encountered.

| Extends                 |
|:------------------------|
| `riscv_asm_program_gen` |


| Implements           | Purpose |
|:---------------------|:--------|
| `gen_program_header` | Sets up initial bootstrap code suitable for the cv32 cores |
| `gen_test_done`      | Reserves registers to be used for end of test status reports, and sets correct values upon test completion |
| `gen_ecall_handler`  | Simple handler that increments mepc and returns to facilitate random ecalls in tests |

--------------------------------------------------------------------------------

#### corev\_directive\_instr

Description:<br>
Enables insertion of compiler directives into the random instruction streams
such as ".option push", ".option pop". This may be used to selectively disable
certain compiler features at certain locations in tests.

| Extends       |
|:--------------|
| `riscv_instr` |

| Implements       | Purpose |
|:-----------------|:--------|
| `convert2asm`    | Enables the insertion of an arbitrary string + comment into the instruction stream|
| `get_instr_name` | Returns directive text as a string |

--------------------------------------------------------------------------------

#### corev\_instr\_base\_test
Description:<br>
Initializes report server, Enables override of default asm-file name

| Extends |
|:--------|
| `riscv_instr_base_test` |

| Implements  | Purpose |
|:------------|:--------|
| `new`       | Initializes report server |
| `run_phase` | generates directed instructions streams |

--------------------------------------------------------------------------------

#### corev\_report\_server
Description:<br>
Implements UVM report server message composer

| Extends                     |
|:----------------------------|
| `uvm_default_report_server` |

| Implements               | Purpose |
|:-------------------------|:--------|
| `compose_report_message` | Creates appropriate log messages for UVM logs |

--------------------------------------------------------------------------------

### Classes implementing instruction streams

--------------------------------------------------------------------------------

#### corev\_compressed\_load\_store\_stress\_instr\_stream
Description:<br>
Generate load store-stream with offsets biased to generate many C\_LW and C\_SW streams,
Improves coverage for compressed load/store instructions.

| Extends                                |
|:---------------------------------------|
| `riscv_load_store_stress_instr_stream` |

| Constrains         | Purpose |
|:-------------------|:--------|
| `sp_c`             | Enable (with randomized probability) use of sp as rs1. |
| `compressed_reg_c` | Restricts rs1 to compressed instruction-addressable registers. |

| Implements         | Purpose |
|:-------------------|:--------|
| `randomize_offset` | Biases load/store address+offset |

--------------------------------------------------------------------------------

#### corev\_compressed\_load\_store\_wfi\_stress\_instr\_stream
Description:<br>
Generate load store-stream with offsets biased to generate many `C_LW` and `C_SW` streams with injected WFIs.
Improves coverage for the combination of compressed load/store instructions in conjunction with WFIs.

| Extends                                           |
|:--------------------------------------------------|
| `corev_compressed_load_store_stress_instr_stream` |

| Constrains   | Purpose |
|:-------------|:--------|
| `wfi_dist_c` | enables first and last instruction of stream to be wfi with a probability 10% |

| Implements       | Purpose |
|:-----------------|:--------|
| `post_randomize` | insert random streams with high probability of `C_LW` and `C_SW` and with injected wfi |

--------------------------------------------------------------------------------

#### corev\_ecall\_instr\_stream
Description:<br>
Directed stream to insert ECALL in tests

| Extends                              |
|:-------------------------------------|
| `riscv_load_store_rand_instr_stream` |

| constrains   | Purpose |
|:-------------|:--------|
| `ecall_c`    | Constrains amount of ECALLs inserted into the instruction stream|
| `wfi_dist_c` | Randomize enable/disable WFI |
| `wfi_cfg_c`  | Constrains WFI to be disabled if commanded by configuration |

| Implements        | Purpose |
|:------------------|:--------|
| `add_mixed_instr` | Adds ECALL and WFIs into random instruction stream |
| `add_wfi`         | Adds WFI instruction |
| `add_ecall`       | Adds ECALL instruction |

--------------------------------------------------------------------------------

#### corev\_interrupt\_csr\_instr\_stream
Description:<br>
Directed stream to inject CLINT-interrupt related CSR writes

| Extends |
|:--------|
| `riscv_load_store_rand_instr_stream` |

| Constrains       | Purpose |
|:-----------------|:--------|
| `ordering_wgt_c` | Ensures correct constraint ordering|
| `dist_action_c`  | Constrains weighting of MIE/mstatus.MIE writes based on configuration |
| `default_wgt_c`  | Default weighting, if none is supplied by configuration |

| Implements                   | Purpose |
|:-----------------------------|:--------|
| `add_mixed_instr`            | Inserts MIE write/mstatus.MIE write into instruction stream |
| `generate_mie_write`         | Generates random MIE write |
| `generate_mstatus_mie_write` | randomly set or clear bit 3 (MIE) in mstatus |

--------------------------------------------------------------------------------

#### corev\_interrupt\_csr\_wfi\_instr\_stream
Description:<br>
Directed stream to inject CLINT-interrupt related CSR writes, but ensures that at least one valid CLINT interrupt is set to avoid starving WFI

| Extends                            |
|:-----------------------------------|
| `corev_interrupt_csr_instr_stream` |

| Constrains | Purpose |
|:-----------|:--------|
| `wfi_c`    | Ensures at least one valid interrupt when randomly setting MIE |

| Implements       | Purpose |
|:-----------------|:--------|
| `post_randomize` | Disallows zero (x0) as rd for LI to avoid clearing MIE |

--------------------------------------------------------------------------------

#### corev\_jal\_wfi\_instr
Description:<br>
Directed stream that uses `riscv_jal_instr` with injected wfi instructions.
Aids in closing coverage for WFI in combination with `C_J` and `JAL` instructions.

| Extends           |
|:------------------|
| `riscv_jal_instr` |

| Constrains  | Purpose |
|:------------|:--------|
| `num_wfi_c` | Constrains number of WFIs inserted into stream 0-3 |

| Implements       | Purpose |
|:-----------------|:--------|
| `post_randomize` | randomly inserts wfi, move jump-targets following a wfi to the wfi itself |

--------------------------------------------------------------------------------

#### corev\_jalr\_wfi\_instr
Description:<br>
Directed stream to close coverage on wfi followed by jump.

| Extends                       |
|:------------------------------|
| `riscv_directed_instr_stream` |

| Constrains    | Purpose |
|:--------------|:--------|
| `use_jalr_c`  | disable stream if ra is reserved as compressed jalr can only use ra for return address |
| `valid_reg_c` | constrain usage of reserved or compressed-incompatible registers                |

| Implements       | Purpose |
|:-----------------|:--------|
| `post_randomize` | adds fixed stream (see below) |
```
    la    s0, 1f
    la    s1, 2f
    wfi
    jalr  zero, s0, 0
 2: c.jal 3f
 1: jalr  zero, s1, 0
 3: nop
```

--------------------------------------------------------------------------------

#### corev\_nop\_instr
Description:<br>
Generate compressed/non-compressed NOPs (pseudo op) and insert into instruction stream.

| Extends                       |
|:------------------------------|
| `riscv_directed_instr_stream` |

| Implements       | Purpose |
|:-----------------|:--------|
| `post_randomize` | randomly insert compressed or non-compressed NOP into instruction stream |

--------------------------------------------------------------------------------

#### corev\_xori\_not\_instr
Description:<br>
Generates XORI with -1 as immediate value to test logical not pseudo-op

| Extends                       |
|:------------------------------|
| `riscv_directed_instr_stream` |

| Implements       | Purpose |
|:-----------------|:--------|
| `post_randomize` | randomly insert XORI with -1 immediate value to test logical not pseudo-op |

--------------------------------------------------------------------------------

