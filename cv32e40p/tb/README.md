## Testbenches for the CV32E40P CORE-V family of RISC-V cores.
There are two distinct testbenches here.

### core
A very simple testbench that can be run with Verilator and any commercial SystemVerilog simulator.
This is not a production testbench - it is here to provide a simple example.

### uvmt
The testbench for the CV32E40P UVM verification environment.
This is the production environment used to verify the CV32E40P.
This testbench must be run with a SystemVerilog 1800-compliant simulator.
