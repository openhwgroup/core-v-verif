/*
 * Copyright 2024 Dolphin Design
 * SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// [Dolphin Design updates]
// Note:
// 1) This file contains streams that use to improve functional coverage holes
// 2) They are optional to be included in regression list

// this stream is to improve func coverage for in uvme_interrupt_covg_v2 by cycle through all cv_* instructions multiple times for irq and wfi coverage purpose - START
class cv32e40p_cv_instrs_multi_loops_streams extends cv32e40p_float_zfinx_base_instr_stream;

  localparam TOTAL_INSTR_C_TYPE     = 27;
  localparam TOTAL_INSTR_X_TYPE     = 304;

  bit                 include_wfi_insn   = 0;
  int unsigned        insert_wfi_cnt     = 0;   
  int unsigned        loop_cnt           = 0;
  int unsigned        total_instr        = 0;
  int unsigned        loop_cnt_limit     = 0;
  int unsigned        ignored_instr_cnt  = 0;

  `uvm_object_utils(cv32e40p_cv_instrs_multi_loops_streams)
  `uvm_object_new

  constraint ovr_c_others {
    num_of_instr_per_stream == total_instr * loop_cnt_limit;
  }

  // manipulate isns list that need to be covered in this stream
  virtual function void init_rand_instr_entry();
    reset_rand_instr_entry();

    include_group   = new[1] ({RV32X});
    exclude_instr   = new[9] ({CV_START, CV_STARTI, CV_END, CV_ENDI, CV_COUNT, CV_COUNTI, CV_SETUP, CV_SETUPI, CV_ELW});

    // these already covered in all cvg, can be ignored meantime - Start (note: users can modify this to focus on insn list to b ecovered)
    ignored_instr_cnt = 4;
    exclude_instr   = new[exclude_instr.size()+ignored_instr_cnt] ({exclude_instr, CV_MAX, CV_ADDN, CV_AVG_SCI_H, CV_SHUFFLEI3_SCI_B});
    // these already covered in all cvg, can be ignored meantime - End

    if (include_load_store_base_sp) begin // cover c_[s|l]wsp insn only
      include_group   = new[include_group.size()+1] ({include_group, RV32C});
      // these already covered in all cvg, can be ignored meantime - Start (note: users can modify this to focus on insn list to b ecovered)
      exclude_instr   = new[exclude_instr.size()+25] ({exclude_instr, C_LW, C_SW, C_ADDI4SPN, C_ADDI, C_LI, C_ADDI16SP, C_LUI,
        C_SRLI, C_SRAI, C_ANDI, C_SUB, C_XOR, C_OR, C_AND, C_BEQZ, C_BNEZ, C_SLLI, C_MV, C_EBREAK, C_ADD, C_NOP, C_J,
        C_JAL, C_JR, C_JALR});
      // these already covered in all cvg, can be ignored meantime - End
    end
    if (include_load_store_base_sp && !is_zfinx) begin // cover c_[fs|fl]wsp insn only
      include_group   = new[include_group.size()+1] ({include_group, RV32FC}); 
      exclude_instr   = new[exclude_instr.size()+2] ({exclude_instr, C_FLW, C_FSW}); // these already covered in all cvg, can be ignored meantime
    end
  endfunction : init_rand_instr_entry

  virtual function void init_iteration_var();
    total_instr = 0; loop_cnt_limit = 0;
    if (!include_wfi_insn)                            total_instr = 2;
    else if (!include_load_store_base_sp)             total_instr = TOTAL_INSTR_X_TYPE - exclude_instr.size();
    else if (include_load_store_base_sp && is_zfinx)  total_instr = TOTAL_INSTR_X_TYPE + TOTAL_INSTR_C_TYPE - exclude_instr.size();
    else if (include_load_store_base_sp && !is_zfinx) total_instr = TOTAL_INSTR_X_TYPE + TOTAL_INSTR_C_TYPE + TOTAL_INSTR_FC_TYPE - exclude_instr.size();
    assert(total_instr > 0);
    loop_cnt_limit    = (include_wfi_insn) ? 1 : 3;
  endfunction: init_iteration_var

  virtual function void update_current_instr_arg_list(int idx=0);
    if (idx == 0) begin
      loop_cnt++; assert (loop_cnt <= loop_cnt_limit);
    end
    else if (idx != 0 && idx%total_instr == 0) begin
      loop_cnt++; assert (loop_cnt <= loop_cnt_limit);
      init_rand_instr_entry(); // reinit for next loop
    end
  endfunction: update_current_instr_arg_list

  virtual function void update_next_instr_arg_list(riscv_instr prev_instr=null, int idx=0);
    if (exclude_instr.size() > 0) begin
      if (use_no_repetitive_instr_per_stream && prev_instr != null) begin
        if (!(prev_instr.instr_name inside {exclude_instr})) 
          exclude_instr = new[exclude_instr.size()+1] ({exclude_instr, prev_instr.instr_name});
        // $display("exclude_instr size is %0d", exclude_instr.size());
      end
    end
    else assert(0);
  endfunction: update_next_instr_arg_list

  function void pre_randomize();
    super.pre_randomize();
    use_fp_only_for_directed_instr      = 0;
    en_clr_fflags_af_instr              = 0;
    include_load_store_base_sp          = 1;
    use_no_repetitive_instr_per_stream  = 1; // expanding exclude_instr per iteration
    init_rand_instr_entry();
    init_iteration_var();
  endfunction: pre_randomize

 function void post_randomize();
 
    riscv_instr                 instr;
    riscv_fp_in_x_regs_instr    instr_zfinx;
    riscv_floating_point_instr  instr_f;

    // print_stream_setting();
    for (int i = 0; i < num_of_instr_per_stream; i++) begin : GEN_N_MANIPULATE_INSTR

      if (include_wfi_insn) begin : INTERLEAVE_INSN_WITH_WFI
        if (i == 0) begin
          `SET_GPR_VALUE(gp_reg_scratch,32'h0000_0008)
          // disable global mie
          directed_csr_access(.instr_name(CSRRC), .rs1(gp_reg_scratch), .csr(12'h300));
          insert_wfi_cnt = $urandom_range(4, 12); 
          insert_wfi_instr(); insert_wfi_cnt--;
        end
        else if (i == num_of_instr_per_stream-1) begin
          // enable global mie - flush all pending interrupts
          directed_csr_access(.instr_name(CSRRS), .rs1(gp_reg_scratch), .csr(12'h300));
          insert_nop_instr(1);
        end
        else if (insert_wfi_cnt == 0) begin
          // enable global mie - flush all pending interrupts
          directed_csr_access(.instr_name(CSRRS), .rs1(gp_reg_scratch), .csr(12'h300));
          insert_nop_instr(1);
          // disable global mie
          directed_csr_access(.instr_name(CSRRC), .rs1(gp_reg_scratch), .csr(12'h300));
          insert_wfi_cnt = $urandom_range(4, 12); 
          insert_wfi_instr(); insert_wfi_cnt--;
        end
        else begin
          insert_wfi_instr(); insert_wfi_cnt--;
        end
      end
      else begin
        /* do nothing */
      end

      update_current_instr_arg_list(i);
      instr = new riscv_instr::get_rand_instr(
        .include_instr(include_instr),
        .exclude_instr(exclude_instr),
        .include_category(include_category),
        .exclude_category(exclude_category),
        .include_group(include_group),
        .exclude_group(exclude_group)
      );
      update_next_instr_arg_list(instr, i);

      assert(instr.group inside {RV32C, RV32FC, RV32X}); // these are the intended groups in this stream
      randomize_gpr(instr);
      if (instr.instr_name inside {`STORE_INSTR_LIST, `FP_STORE_INSTR_LIST})
        store_instr_gpr_handling(instr);

      instr.comment = $sformatf(" Inserted %0s - idx[%0d]", get_name(), i);
      instr_list.push_back(instr);
    end // num_of_instr_per_stream

 endfunction: post_randomize

endclass: cv32e40p_cv_instrs_multi_loops_streams

class cv32e40p_cv_instrs_w_wfi_multi_loops_streams extends cv32e40p_cv_instrs_multi_loops_streams;

  `uvm_object_utils(cv32e40p_cv_instrs_w_wfi_multi_loops_streams)
  `uvm_object_new

  function void pre_randomize();
    include_wfi_insn = 1;
    super.pre_randomize();
  endfunction: pre_randomize

endclass: cv32e40p_cv_instrs_w_wfi_multi_loops_streams
// this stream is to improve func coverage for in uvme_interrupt_covg_v2 by cycle through all cv_* instructions multiple times for irq and wfi coverage purpose - END


// this stream is to improve func coverage for in uvme_rv32x_hwloop_covg - START
class cv32e40p_xpulp_single_hwloop_stream_directed extends cv32e40p_xpulp_hwloop_base_stream;

  `uvm_object_utils(cv32e40p_xpulp_single_hwloop_stream_directed)
  `uvm_object_new
  
  constraint gen_hwloop_count_c {
    solve num_loops_active before gen_nested_loop;
    solve gen_nested_loop  before hwloop_count, hwloop_counti;
    solve num_hwloop_instr before hwloop_count, hwloop_counti;
    gen_nested_loop == 0;
    num_loops_active == 1;
    foreach(hwloop_count[i]) {
      if (num_hwloop_instr[i] == 3) {
        hwloop_count[i]  == 4095;
      }
      else {
        hwloop_count[i]  inside {401, 1024};
      }
      hwloop_counti[i] == hwloop_count[i];
    }
  }

  constraint no_imm_hwloop_setup_instr_c {
      use_loop_counti_inst[0] == 0;
      use_loop_counti_inst[1] == 0;
      use_loop_setupi_inst[0] == 0;
      use_loop_setupi_inst[1] == 0;
  }

  constraint num_hwloop_instr_c {
    solve use_loop_endi_inst before num_hwloop_instr;
    foreach (num_hwloop_instr[i]) {
      // the max setting of Uimm[11:0] is 4092 however the the hwloop start label is not immediately following after cv.endi, 
      // there is randomize numberof instr inserted between cv.endi and hwloop start label we need to keep some buffer from 
      // max value so that the number instr can never be max 4092 (-5 buffer for instrs prior hwloop)
      if (use_loop_endi_inst[i]) {
        num_hwloop_instr[i] dist { 3 := 1, 3074 := 5, 4087 := 1 };
      } else {
        num_hwloop_instr[i] dist { 3 := 1, 3074 := 5, 4092 := 1 };
      }
      num_fill_instr_loop_ctrl_to_loop_start[i] inside {[0:7]};
    }
    num_fill_instr_in_loop1_till_loop0_setup == 0;
  }

endclass : cv32e40p_xpulp_single_hwloop_stream_directed
// this stream is to improve func coverage for in uvme_rv32x_hwloop_covg - END

// this stream is to improve func coverage for in uvme_debug_covg - START
class cv32e40p_fp_only_fdiv_fsqrt_stream extends cv32e40p_fp_n_mixed_instr_stream;

  `uvm_object_utils(cv32e40p_fp_only_fdiv_fsqrt_stream)
  `uvm_object_new

  function void pre_randomize();
    super.pre_randomize();
    use_fp_only_for_directed_instr  = 1;
    use_only_for_fdiv_fsqrt_gen     = 1;
    en_clr_fflags_af_instr          = 0;
  endfunction: pre_randomize

  virtual function void add_instr_prior_directed_instr(riscv_instr instr, int idx=0);
    if ($test$plusargs("add_b2b_illegal_insn")) begin
      insert_illegal_instr();
    end
    super.add_instr_prior_directed_instr(instr, idx);
  endfunction : add_instr_prior_directed_instr

endclass: cv32e40p_fp_only_fdiv_fsqrt_stream
// this stream is to improve func coverage for in uvme_debug_covg - END
