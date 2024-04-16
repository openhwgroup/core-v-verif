# Copyright 2024 Torje Nygaard Eikenes
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
# not use this file except in compliance with the License, or, at your option,
# the Apache License version 2.0.
#
# You may obtain a copy of the License at
# https://solderpad.org/licenses/SHL-2.1/
#
# Unless required by applicable law or agreed to in writing, any work
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#
# See the License for the specific language governing permissions and
# limitations under the License.


# Must currently be run with COREV_ASSERT_OFF defined to disable binded assertions in cv32e40s_wrapper.sv.
# In onespin, binding to individual instances is only supported when used with 
# read_sva, but not with read_verilog, which is used to load all the files.
# TODO: remove binding to individual instances or use read_sva after compilation to load assertions.


# Include relevant environment variables
set CV_CORE_PKG             $env(CV_CORE_PKG)
set DV_ISA_DECODER_PATH     $env(DV_ISA_DECODER_PATH)
set DV_SUPPORT_PATH         $env(DV_SUPPORT_PATH)
set DV_UVM_TESTCASE_PATH    $env(DV_UVM_TESTCASE_PATH)
set DV_UVMA_PATH            $env(DV_UVMA_PATH)
set DV_UVME_PATH            $env(DV_UVME_PATH)
set DV_UVMT_PATH            $env(DV_UVMT_PATH)
set DESIGN_RTL_DIR          $env(DESIGN_RTL_DIR)

proc cvfv_rerun {} {
    delete_design -golden
    start_message_log -force onespin.log
    
    # global env is used to also enable environment variables inside the procedure. 
    global env CV_CORE_PKG
    global env DV_ISA_DECODER_PATH  
    global env DV_SUPPORT_PATH      
    global env DV_UVM_TESTCASE_PATH 
    global env DV_UVMA_PATH         
    global env DV_UVME_PATH         
    global env DV_UVMT_PATH         
    global env DESIGN_RTL_DIR

    # Include files from fv.flist
    # vlog -sv -f fv.flist 
    # ^ Not used because sv2012 can not be set and has a bug(?) where it uses 
    #   set_read_hdl_option instead of add_read_hdl_option, overwriting the 
    #   include paths when setting "set_read_hdl_option -verilog_compilation_unit one".
    # TODO: Contact Onespin about this

    # Instead we manually import all the files from fv.flist below

    set_read_hdl_option -verilog_compilation_unit ext

    # Include paths from fv.flist
    add_read_hdl_option -verilog_include_path $DV_UVMT_PATH

    add_read_hdl_option -verilog_include_path $DV_UVME_PATH
    add_read_hdl_option -verilog_include_path $DV_UVMA_PATH/uvma_rvfi
    add_read_hdl_option -verilog_include_path $DV_UVMA_PATH/uvma_fencei
    add_read_hdl_option -verilog_include_path $DV_UVMA_PATH/uvma_clic
    add_read_hdl_option -verilog_include_path $DV_UVMA_PATH/uvma_obi_memory/src



    # Files from fv.flist
    read_verilog -golden -version sv2012 {
        ./uvm_pkg.sv 
        ./defines.sv

    }

    # Files from cv32e40s_manifest.flist
    add_read_hdl_option -verilog_include_path $DESIGN_RTL_DIR/include
    add_read_hdl_option -verilog_include_path $DESIGN_RTL_DIR/../bhv
    add_read_hdl_option -verilog_include_path $DESIGN_RTL_DIR/../bhv/include
    add_read_hdl_option -verilog_include_path $DESIGN_RTL_DIR/../sva

    # TEMP: define COREV_ASSERT_OFF to disable binded assertions in cv32e40s_wrapper.sv
    read_verilog -golden -version sv2012 -define {COREV_ASSERT_OFF} {
        $DESIGN_RTL_DIR/include/cv32e40s_pkg.sv
        $DESIGN_RTL_DIR/cv32e40s_if_c_obi.sv
        $DESIGN_RTL_DIR/../bhv/include/cv32e40s_rvfi_pkg.sv
        $DESIGN_RTL_DIR/../bhv/cv32e40s_wrapper.sv
        $DESIGN_RTL_DIR/cv32e40s_dummy_instr.sv
        $DESIGN_RTL_DIR/cv32e40s_if_stage.sv
        $DESIGN_RTL_DIR/cv32e40s_csr.sv
        $DESIGN_RTL_DIR/cv32e40s_debug_triggers.sv
        $DESIGN_RTL_DIR/cv32e40s_cs_registers.sv
        $DESIGN_RTL_DIR/cv32e40s_register_file.sv
        $DESIGN_RTL_DIR/cv32e40s_register_file_ecc.sv
        $DESIGN_RTL_DIR/cv32e40s_register_file_wrapper.sv
        $DESIGN_RTL_DIR/cv32e40s_write_buffer.sv
        $DESIGN_RTL_DIR/cv32e40s_lsu_response_filter.sv
        $DESIGN_RTL_DIR/cv32e40s_load_store_unit.sv
        $DESIGN_RTL_DIR/cv32e40s_id_stage.sv
        $DESIGN_RTL_DIR/cv32e40s_i_decoder.sv
        $DESIGN_RTL_DIR/cv32e40s_m_decoder.sv
        $DESIGN_RTL_DIR/cv32e40s_b_decoder.sv
        $DESIGN_RTL_DIR/cv32e40s_decoder.sv
        $DESIGN_RTL_DIR/cv32e40s_compressed_decoder.sv
        $DESIGN_RTL_DIR/cv32e40s_sequencer.sv
        $DESIGN_RTL_DIR/cv32e40s_alignment_buffer.sv
        $DESIGN_RTL_DIR/cv32e40s_prefetch_unit.sv
        $DESIGN_RTL_DIR/cv32e40s_mult.sv
        $DESIGN_RTL_DIR/cv32e40s_int_controller.sv
        $DESIGN_RTL_DIR/cv32e40s_clic_int_controller.sv
        $DESIGN_RTL_DIR/cv32e40s_ex_stage.sv
        $DESIGN_RTL_DIR/cv32e40s_wb_stage.sv
        $DESIGN_RTL_DIR/cv32e40s_div.sv
        $DESIGN_RTL_DIR/cv32e40s_alu.sv
        $DESIGN_RTL_DIR/cv32e40s_ff_one.sv
        $DESIGN_RTL_DIR/cv32e40s_popcnt.sv
        $DESIGN_RTL_DIR/cv32e40s_alu_b_cpop.sv
        $DESIGN_RTL_DIR/cv32e40s_controller_fsm.sv
        $DESIGN_RTL_DIR/cv32e40s_controller_bypass.sv
        $DESIGN_RTL_DIR/cv32e40s_controller.sv
        $DESIGN_RTL_DIR/cv32e40s_obi_integrity_fifo.sv
        $DESIGN_RTL_DIR/cv32e40s_instr_obi_interface.sv
        $DESIGN_RTL_DIR/cv32e40s_data_obi_interface.sv
        $DESIGN_RTL_DIR/cv32e40s_prefetcher.sv
        $DESIGN_RTL_DIR/cv32e40s_sleep_unit.sv
        $DESIGN_RTL_DIR/cv32e40s_alert.sv
        $DESIGN_RTL_DIR/cv32e40s_core.sv
        $DESIGN_RTL_DIR/cv32e40s_mpu.sv
        $DESIGN_RTL_DIR/cv32e40s_pma.sv
        $DESIGN_RTL_DIR/cv32e40s_pmp.sv
        $DESIGN_RTL_DIR/cv32e40s_pc_target.sv
        $DESIGN_RTL_DIR/cv32e40s_wpt.sv
        $DESIGN_RTL_DIR/cv32e40s_pc_check.sv
        $DESIGN_RTL_DIR/cv32e40s_rchk_check.sv
        $DESIGN_RTL_DIR/cv32e40s_lfsr.sv

        $DESIGN_RTL_DIR/../bhv/cv32e40s_sim_sffr.sv
        $DESIGN_RTL_DIR/../bhv/cv32e40s_sim_sffs.sv
        $DESIGN_RTL_DIR/../bhv/cv32e40s_sim_clock_gate.sv
        $DESIGN_RTL_DIR/../bhv/cv32e40s_rvfi_instr_obi.sv
        $DESIGN_RTL_DIR/../bhv/cv32e40s_rvfi_data_obi.sv
        $DESIGN_RTL_DIR/../bhv/cv32e40s_rvfi.sv
        $DESIGN_RTL_DIR/../bhv/cv32e40s_rvfi_sim_trace.sv

    } 
    
    # Files from isa_decoder_pgk.flist
    add_read_hdl_option -verilog_include_path $DV_ISA_DECODER_PATH
    # define QUESTA_VSIM to fix error in isa_decoder_pkg.sv
    read_verilog -golden  -version sv2012 -define {QUESTA_VSIM} {
        $DV_ISA_DECODER_PATH/isa_decoder_pkg.sv
    }

    # Files from support_pkg.flist
    add_read_hdl_option -verilog_include_path $DV_SUPPORT_PATH

    read_verilog -golden -version sv2012 {
        $DV_SUPPORT_PATH/support_pkg.sv
    }


    # Files from fv.flist
    read_verilog -golden -version sv2012 {

        $DV_UVM_TESTCASE_PATH/base-tests/uvmt_cv32e40s_base_test_pkg.sv
        $DV_UVMA_PATH/uvma_obi_memory/src/uvma_obi_memory_assert.sv
        $DV_UVMA_PATH/uvma_obi_memory/src/uvma_obi_memory_1p2_assert.sv
        
        ./dummy_pkg.sv

        $DV_UVMA_PATH/uvma_clic/uvma_clic_if.sv
        $DV_UVMA_PATH/uvma_debug/uvma_debug_if.sv
        $DV_UVMA_PATH/uvma_fencei/uvma_fencei_if.sv
        $DV_UVMA_PATH/uvma_interrupt/uvma_interrupt_if.sv
        $DV_UVMA_PATH/uvma_obi_memory/src/uvma_obi_memory_assert_if_wrp.sv
        $DV_UVMA_PATH/uvma_obi_memory/src/uvma_obi_memory_if.sv
        $DV_UVMA_PATH/uvma_rvfi/uvma_rvfi_csr_if.sv
        $DV_UVMA_PATH/uvma_rvfi/uvma_rvfi_instr_if.sv
        $DV_UVMA_PATH/uvma_wfe_wu/uvma_wfe_wu_if.sv
        $DV_UVME_PATH/uvme_cv32e40s_core_cntrl_if.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_tb_ifs.sv

        $DV_UVMT_PATH/uvmt_cv32e40s_dut_wrap.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_tb.sv

        $DV_UVMT_PATH/../assertions/uvmt_cv32e40s_fencei_assert.sv
        $DV_UVMT_PATH/../assertions/uvmt_cv32e40s_pmp_assert.sv
        $DV_UVMT_PATH/../assertions/uvmt_cv32e40s_pmprvfi_assert.sv
        $DV_UVMT_PATH/../assertions/uvmt_cv32e40s_rvfi_assert.sv
        $DV_UVMT_PATH/../assertions/uvmt_cv32e40s_umode_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_clic_interrupt_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_debug_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_integration_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_interrupt_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_pma_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_triggers_assert_cov.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_xsecure_assert/uvmt_cv32e40s_xsecure_bus_protocol_hardening_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_xsecure_assert/uvmt_cv32e40s_xsecure_data_independent_timing_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_xsecure_assert/uvmt_cv32e40s_xsecure_dummy_and_hint_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_xsecure_assert/uvmt_cv32e40s_xsecure_hardened_csrs_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_xsecure_assert/uvmt_cv32e40s_xsecure_hardened_csrs_clic_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_xsecure_assert/uvmt_cv32e40s_xsecure_hardened_csrs_interrupt_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_xsecure_assert/uvmt_cv32e40s_xsecure_hardened_csrs_pmp_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_xsecure_assert/uvmt_cv32e40s_xsecure_hardened_pc_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_xsecure_assert/uvmt_cv32e40s_xsecure_interface_integrity_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_xsecure_assert/uvmt_cv32e40s_xsecure_reduced_profiling_infrastructure_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_xsecure_assert/uvmt_cv32e40s_xsecure_register_file_ecc_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_xsecure_assert/uvmt_cv32e40s_xsecure_security_alerts_assert.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_zc_assert.sv

        $DV_UVMT_PATH/../assertions/uvmt_cv32e40s_pma_model.sv
        $DV_UVMT_PATH/../assertions/uvmt_cv32e40s_pmp_model.sv
        $DV_UVMT_PATH/../assertions/uvmt_cv32e40s_rvfi_cov.sv
        $DV_UVMT_PATH/../assertions/uvmt_cv32e40s_umode_cov.sv
        $DV_UVMT_PATH/support_logic/uvmt_cv32e40s_rchk_shim.sv
        $DV_UVMT_PATH/support_logic/uvmt_cv32e40s_sl_fifo.sv
        $DV_UVMT_PATH/support_logic/uvmt_cv32e40s_sl_obi_phases_monitor.sv
        $DV_UVMT_PATH/support_logic/uvmt_cv32e40s_sl_trigger_match.sv
        $DV_UVMT_PATH/support_logic/uvmt_cv32e40s_sl_trigger_match_mem.sv
        $DV_UVMT_PATH/support_logic/uvmt_cv32e40s_support_logic.sv
        $DV_UVMT_PATH/uvmt_cv32e40s_pma_cov.sv
    }
    
    # Elaborate
    set_elaborate_option -top uvmt_cv32e40s_tb
    elaborate

    # Compile

    # Cutpoints for reset and clock
    add_compile_option -cut_signal clknrst_if/reset_n
    add_compile_option -cut_signal clknrst_if/clk

    # Cutpoints for general control signals
    add_compile_option -cut_signal debug_if/debug_req
    add_compile_option -cut_signal interrupt_if/irq

    # Cutpoints for the OBI interface
    add_compile_option -cut_signal obi_instr_if/err
    add_compile_option -cut_signal obi_instr_if/gntpar
    add_compile_option -cut_signal obi_instr_if/gnt
    add_compile_option -cut_signal obi_instr_if/rchk
    add_compile_option -cut_signal obi_instr_if/rdata
    add_compile_option -cut_signal obi_instr_if/rvalidpar
    add_compile_option -cut_signal obi_instr_if/rvalid
    add_compile_option -cut_signal obi_data_if/err
    add_compile_option -cut_signal obi_data_if/gntpar
    add_compile_option -cut_signal obi_data_if/gnt
    add_compile_option -cut_signal obi_data_if/rchk
    add_compile_option -cut_signal obi_data_if/rdata
    add_compile_option -cut_signal obi_data_if/rvalidpar
    add_compile_option -cut_signal obi_data_if/rvalid
    add_compile_option -cut_signal fencei_if/flush_ack

    compile

    set_mode mv

    #TODO: Find a way to use read_sva to load assertion from cv32e40s_wrapper.sv
}

cvfv_rerun