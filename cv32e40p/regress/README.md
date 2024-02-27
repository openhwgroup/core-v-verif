CV32E40P Regress Files
==================================

For V2 core, all the regressions files should be generated using the following cv_regress commands, where *type* has to be chosen between `sh` and `rmdb`, and *sim* is the wanted simulator (vsim, xrun, ...)

## pulp configuration

> ./cv_regress --{type} --file=cv32e40pv2_xpulp_instr.yaml --simulator={sim} --outfile=xpulp_instr_pulp.{type} --cfg pulp <br>
> ./cv_regress --{type} --file=cv32e40pv2_interrupt_debug.yaml --simulator={sim} --outfile=int_debug_pulp.{type} --cfg pulp<br>

## pulp_fpu configuration
> ./cv_regress --{type} --file=cv32e40pv2_xpulp_instr.yaml --simulator={sim} --outfile=xpulp_instr_pulp_fpu.{type} --cfg pulp_fpu --add_test_cfg floating_pt_instr_en<br>
> ./cv_regress --{type} --file=cv32e40pv2_fpu_instr.yaml --simulator={sim} --outfile=fpu_instr_pulp_fpu.{type} --cfg pulp_fpu --add_test_cfg floating_pt_instr_en<br>
> ./cv_regress --{type} --file=cv32e40pv2_interrupt_debug.yaml --simulator={sim} --outfile=int_debug_pulp_fpu.{type} --cfg pulp_fpu --add_test_cfg floating_pt_instr_en<br>

## pulp_fpu_zfinx configuration
> ./cv_regress --{type} --file=cv32e40pv2_xpulp_instr.yaml --simulator={sim} --outfile=xpulp_instr_pulp_fpu_zfinx.{type} --cfg pulp_fpu_zfinx --add_test_cfg floating_pt_zfinx_instr_en<br>
> ./cv_regress --{type} --file=cv32e40pv2_fpu_instr.yaml --simulator={sim} --outfile=fpu_instr_pulp_fpu_zfinx.{type} --cfg pulp_fpu_zfinx --add_test_cfg floating_pt_zfinx_instr_en<br>
> ./cv_regress --{type} --file=cv32e40pv2_interrupt_debug.yaml --simulator={sim} --outfile=int_debug_pulp_fpu_zfinx.{type} --cfg pulp_fpu_zfinx --add_test_cfg floating_pt_zfinx_instr_en<br>

## configurations with latency
To generate regressions with latency (e.g. pulp_fpu_zfinx_2cyclat), only the `--cfg` switch has to be updated:

> ./cv_regress --{type} --file=cv32e40pv2_xpulp_instr.yaml --simulator={sim} --outfile=xpulp_instr_pulp_fpu_zfinx_2cyclat.{type} --cfg pulp_fpu_zfinx_2cyclat --add_test_cfg floating_pt_zfinx_instr_en<br>
> ./cv_regress --{type} --file=cv32e40pv2_fpu_instr.yaml --simulator={sim} --outfile=fpu_instr_pulp_fpu_zfinx_2cyclat.{type} --cfg pulp_fpu_zfinx_2cyclat --add_test_cfg floating_pt_instr_en<br>
> ./cv_regress --{type} --file=cv32e40pv2_interrupt_debug.yaml --simulator={sim} --outfile=int_debug_pulp_fpu_zfinx_2cyclat.{type} --cfg pulp_fpu_zfinx_2cyclat --add_test_cfg floating_pt_instr_en
