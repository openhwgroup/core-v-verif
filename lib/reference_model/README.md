# Reference Model

The reference model is built as a shell around Spike, with the goal of properly simulating asynchronous events.

Spike is responsible for the functional execution, while the pipeline shell is responsible for timing interrupts and other asynchronous events, and timing the RVFI output for comparison with the core.

TODO: Add a more detailed explenation

## Usage 

To run the reference model alongside cv32e40s, run `make` as normal, but include the following:
- Export `SPIKE_PATH=<path to riscv/riscv-isa-sim>` to use another spike version. If not set, spike from `vendor/riscv/riscv-isa-sim` will be used.

- set `USE_ISS=YES ISS=RM` to enable the reference model.

For example:
`export SPIKE_HOME=~/core-v-verif/vendor/riscv/riscv-isa-sim`
`make test TEST=hello-world ISS=YES ISS=RM`

