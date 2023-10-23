## Xcelium Tools Directory

Xcelium-based utilities and scripts.


### Simulator Control Scripts

These scripts can be passed to Xcelium by the core-v-verif Makefiles.
The following scripts are currently supported:

| Script     | Usage |
|------------|-------|
| probe.tcl  | Generates probes for waveform database viewable with Cadence SimVision.  Invoked when WAVES=1 passed to the make test command |
| indago.tcl | Generates probes for waveform database viewable with Cadence Indago.  Invokedf when WAVES=1 ADV_DEBUG=1 passed to the make test command |


### Coverage Refinement Files

These refinement files should be created using coverage tools such as IMC or Vmanager.
They are used to generate coverage reports that focus on necessary coverage, while removing exceptions that are unhittable or not significant for the design being verified.

*Note that some files are automatically generated and some are manually maintained.  This is indicated in the table.*

| File                              | Maintenance | Description |
|-----------------------------------|-------------|-------------|
| cv32e40s.non_dut_code_cov.vRefine | Manual      | Removes non-DUT code coverage from coverage database, that are not to be considered for coverage (e.g. testbench) |
| cv32e40s.auto.vRefine             | Automatic   | Auto-generated refinements based on parameter usage for the CV32E40S without PULP extensions.  *Do not manually edit* |
| cv32e40s.manual.vRefine           | Manual      | Manually added coverage exception based on deesign verification reviews. |
