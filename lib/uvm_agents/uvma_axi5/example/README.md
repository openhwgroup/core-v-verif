# AXI master to slave example
## Introduction
In this example, an axi master agent is connected to axi slave agent. This example alows a fast verification of changes made in the AXI agent. 

# Usage
To compile and run using VCS: 
python3 $CORE_V_VERIF/lib/cv_dv_utils/python/sim_cmd/compile.py --yaml simulator_vcs.yaml --outdir out
python3 $CORE_V_VERIF/lib/cv_dv_utils/python/sim_cmd/run_test.py --yaml simulator_vcs.yaml --test_name bursty_test_c

To compile and run using questa 
python3 $CORE_V_VERIF/lib/cv_dv_utils/python/sim_cmd/compile.py --yaml simulator_questa.yaml --outdir out
python3 $CORE_V_VERIF/lib/cv_dv_utils/python/sim_cmd/run_test.py --yaml simulator_questa.yaml --test_name bursty_test_c

