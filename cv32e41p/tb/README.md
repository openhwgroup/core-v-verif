## Testbenches for the CV32E41P CORE-V core.
Derived from the
[tb](https://github.com/openhwgroup/core-v-verif/tree/master/cv32e40p/tb)
directory of the OpenHW Group CORE-V project.
There are two distinct testbenches:

### core
Simple test environment that supports self checking test programs.
This testbench can be run using Verilator.

### uvmt
The testbench and testharness for the CV32E40P UVM verification
environments.  This tb/th maintains support for all features of the `core`
testbench.  This testbench must be run with a SystemVerilog 1800-compliant simulator, 
i.e. it cannot be run with Verilator.
<br>
Note: the UVM enivonment for the CV32E41P is not yet available.
