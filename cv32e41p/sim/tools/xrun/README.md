## Xcelium tools directory

Various Xcelium-based utilities and scripts.

### Simulator control scripts

These TCL scripts can be passed to Xcelium by the core-v-verif Makefiles when using Xcelium.  The following scripts are currently supported:

| Script | Usage |
|--------|-------|
| probe.tcl | Generates probes for waveform database viewable with Cadence SimVision.  Invoked when WAVES=1 passed to the make test command |
| indago.tcl | Generates probes for waveform database viewable with Cadence Indago.  Invoked when WAVEs=1 ADV_DEBUG=1 passed to the make test command |

### Coverage refinement files

These have been removed because they are very specific to the CV32E40P and it is expected that CV32E41P will not use them.
