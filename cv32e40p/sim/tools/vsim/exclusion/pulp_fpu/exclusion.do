# functional : assertion and directive 
do ../cv32e40pv2_func_asrt_n_directive_waiver.do

# functional: uvme_interrupt_covg_v2
do ../cv32e40pv2_func_uvme_interrupt_waiver.do

# functional: uvme_debug_covg
do ../cv32e40pv2_func_uvme_debug_waiver.do

# code coverage : common waiver
do ../cv32e40pv2_code_all_cfg_waiver.do

# code coverage : fpu cfg specific waiver
do ../cv32e40pv2_code_fpu_cfg_waiver.do
