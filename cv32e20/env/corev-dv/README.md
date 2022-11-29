## corev-dv
This directory contains core-v-verif extensions to the [riscv-dv](https://github.com/google/riscv-dv) instruction stream generator.
The cloned code from Google is not locally modified, and as much as is possible we attempt to use the latest-and-greatest from Google.
Any core-v-verif specializations are implemented as either replacements (e.g. the manifest) or (perferably) extensions of specific SV classes.
<br><br>
The UVM environments in core-v-verif do not use riscv-dv's `run.py` python script to run the generator (although no changes are made preventing _you_ from doing so).
Check out the appropriate Makefile(s) for an example of how core-v-verif runs the generator.
