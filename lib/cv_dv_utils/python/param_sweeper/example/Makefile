# ----------------------------------------------------------------------------
# Copyright 2023 CEA*
# *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
#
# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#[END OF HEADER]
# ----------------------------------------------------------------------------

########################################################
# Working Library
########################################################
WORK_LIB = cv_uvm_dv_utils_lib

########################################################
# List libraries for simulation
########################################################
LIB_LIST := -L cv_uvm_dv_utils_lib

run_tb_vsim:
	$(CV_DV_UTILS_DIR)/python/param_sweeper/scripts/param_sweeper.py --json example.json --i example_template.txt --o Prefix1 --i example_template_2.txt --o Prefix2
	vlog -64 ${LIB_LIST} -work $(WORK_LIB) -sv $(CV_DV_UTILS_DIR)/uvm/unix_utils/unix_utils_pkg.sv
	vlog -64 ${LIB_LIST} -work $(WORK_LIB) -sv $(CV_DV_UTILS_DIR)/python/param_sweeper/example/param_sweeper_pkg.sv
	vlog -64 ${LIB_LIST} -work $(WORK_LIB) -sv $(CV_DV_UTILS_DIR)/python/param_sweeper/example/tb.sv
	vopt -64 ${LIB_LIST} -work $(WORK_LIB) -o opt tb
	vsim -64 +UVM_NO_RELNOTES ${LIB_LIST} -sv_seed random -c -work $(WORK_LIB) opt -do "run -all ; exit";

run_tb_xrun:
	$(CV_DV_UTILS_DIR)/python/param_sweeper/scripts/param_sweeper.py --json example.json --i example_template.txt --o Prefix1 --i example_template_2.txt --o Prefix2
	xrun -64BIT -WORK $(WORK_LIB) -svseed random -incdir $(CV_DV_UTILS_DIR)/uvm/unix_utils -incdir $(CV_DV_UTILS_DIR)/python/param_sweeper/example -uvm $(CV_DV_UTILS_DIR)/uvm/unix_utils/unix_utils_pkg.sv $(CV_DV_UTILS_DIR)/python/param_sweeper/example/param_sweeper_pkg.sv $(CV_DV_UTILS_DIR)/python/param_sweeper/example/tb.sv
	
run_tb_vcs:
	$(CV_DV_UTILS_DIR)/python/param_sweeper/scripts/param_sweeper.py --json example.json --i example_template.txt --o Prefix1 --i example_template_2.txt --o Prefix2
	vcs -timescale=1ns/1ns -sverilog  +incdir+$(CV_DV_UTILS_DIR)/uvm/unix_utils +incdir+$(CV_DV_UTILS_DIR)/python/param_sweeper/example -ntb_opts uvm-1.2 -l comp.log -v $(WORK_LIB) -l vcs_comp.log $(CV_DV_UTILS_DIR)/uvm/unix_utils/unix_utils_pkg.sv $(CV_DV_UTILS_DIR)/python/param_sweeper/example/param_sweeper_pkg.sv $(CV_DV_UTILS_DIR)/python/param_sweeper/example/tb.sv
	./simv -l vcs_sim.log +ntb_random_seed_automatic +ntb_stop_on_constraint_solver_error=0

run_tb_vsim_hpdcache:
	#$(CV_DV_UTILS_DIR)/python/param_sweeper/scripts/param_sweeper.py --json hpdcache_param.json --i hpdcache_pkg_template.sv --o HPDCACHE_
	vlog -64 ${LIB_LIST} -work $(WORK_LIB) -sv $(CV_DV_UTILS_DIR)/uvm/unix_utils/unix_utils_pkg.sv
	vlog -64 ${LIB_LIST} -work $(WORK_LIB) -sv $(CV_DV_UTILS_DIR)/python/param_sweeper/example/param_sweeper_pkg.sv
	vlog -64 ${LIB_LIST} -work $(WORK_LIB) -sv $(CV_DV_UTILS_DIR)/python/param_sweeper/example/tb.sv
	vopt -64 ${LIB_LIST} -work $(WORK_LIB) -o opt tb
	vsim -64 +UVM_NO_RELNOTES ${LIB_LIST} -sv_seed random -c -work $(WORK_LIB) opt -do "run -all ; exit";
