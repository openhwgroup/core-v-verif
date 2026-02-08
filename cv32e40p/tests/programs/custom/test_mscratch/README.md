# test_mscratch

## Description

`test_mscratch` is a directed test for the CV32E40P core that verifies
full 32-bit read and write access to the `mscratch` CSR (Control and Status Register).

The test performs the following:

- Writes multiple 32-bit patterns to CSR address `0x340` (mscratch)
- Reads back the value after each write
- Compares the readback value against the expected pattern
- Exits with `EXIT_SUCCESS` if all patterns match
- Exits with `EXIT_FAILURE` if any mismatch occurs

## Directory Location

This test is located at: core-v-verif/cv32e40p/tests/programs/custom/test_mscratch

## Verfication using Verilator

Navigate to core-v-verif/cv32e40p/sim/core and run the command `make veri-test TEST=test_mscratch`.

