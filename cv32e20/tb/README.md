## TB: testbench for the CV32E20 CORE-V core.
There are two distinct testbenches:

### core
A very simple testbench that can be run under Verilator.

### uvmt
The testbench and testharness for the CV32EE20 UVM verification environment.
This testbench must be run with a SystemVerilog 1800-compliant simulator, i.e. it cannot be run with Verilator.
