## DV UTILS

This repository provides a set of verification utilities to be used for
simulating digital designs. The bulk of the code consists of UVM utilities
including agents (AXI4,...) and other modules such as reset/clock
generation and memory response generation. The directory structure is organized
by the language of the brick (UVM, SystemVerilog, Python, Perl) and the table
below provides a summary of the available bricks.

| Block | Language | Description |
|-------|:--------:|-------------|
| AXI Superset Agent | UVM | AXI-4 agent with support for atomics. |
| Back Pressure Generator | UVM | Controls a single bit backpressure signal with random sequences. |
| Clock Generator | UVM | Clock generator with controllable frequency |
| Clock Monitor | UVM | Clock monitor that checks a clock is running at the correct frequency, without glitches. |
| DRAM Monitor | UVM | Monitors row/column transactions and build back memory transactions. |
| Generic Agent | UVM | An agent which can be configured for arbitrary data-structure. |
| Memory Partition | UVM | Generates a set of regions in memory. Used to focus accesses into small regions to increase hazard conditions. |
|  Memory Response Model | UVM | An active agent that replaces a real memory system (DRAM controller), generating random, out-of-order responses, but with coherent data |
|  Memory Shadow | UVM | Used to create scoreboards for a memory system. |
|  Perfomance Monitor | UVM | Used to calculate bandwidth and transaction rate between a set of sources and destinations (on a NoC, for example. |
|  Reset Generator | UVM | Generates reset signal during the UVM reset phase. |
|  Unix Utils | UVM | Emulate unix functions in uvm - such a grep/sed or generating unique temporary file names. |
|  Watchdog| UVM | Serves as a watchdog in a testbench. Timeout can come from test-bench or command line. |
|  PLL Model | SystemVerilog | Acts as behavioural model of a PLL, providing high frequency clocks, from a reference. |
|  Random Delay | SystemVerilog | Inserts a random delay on a bus, typically used for verifying multi-cycle paths in RTL simulation. |
|  X-Filter | SystemVerilog | Replaces X's on a bus with random values - use with caution. |
|  Param Sweeper | Python | Generates multiple configurations for simulating paramterized designs. |
|  scan_logs | Perl | Script for parsing log files, reporting errors and warnings, and generating summary reports. |

## Usage

Several of the utilities depend on the environment variabe
$CV_DV_UTILS_DIR pointing to the root of the repository (the directory where this
file resides). Below, we provide the syntax to set the environment variable,
but replace <this directory> with the correction directory for your system.

#### tcsh
```tcsh
setenv CV_DV_UTILS_DIR <this directory>
```

#### bash
```bash
export CV_DV_UTILS_DIR=<this directory>
```

## Licensing
dv_utils is released under the Apache License, Version 2.0.
Please refer to the [LICENSE](LICENSE) file for further information.
