/*
 * Copyright 2018 Google LLC
 * Copyright 2020 OpenHW Group
 * Copyright 2023 Dolphin Design
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

//------------------------------------------------------------------------------
// CORE-V instruction generator configuration class:
//     - extension of the RISC-V instruction generator base test.
//
// The base test Uses the factory to replace riscv_instr_gen_config with corev_instr_gen_config
//------------------------------------------------------------------------------

class cv32e40p_instr_gen_config extends riscv_instr_gen_config;

  // External config control (plusarg) to enable/disable fast_interrupt handlers
  bit enable_fast_interrupt_handler;

  // Knob to set zero fast interrupt handler
  // Knob is needed because FIXED MTVEC mode won't work with fast interrupt handlers
  rand bit knob_zero_fast_intr_handlers;

  // Mask for using a fast interrupt handler (mret only), relying on h/W interrupt ack mechanism
  rand bit [31:0] use_fast_intr_handler;

  // Random register for debug stack pointer
  rand riscv_reg_t     dp;

  // Config for random selection of directed_instr stream from
  // rand_directed_instr_* passed from test plusargs
  bit insert_rand_directed_instr_stream = 0;

  // Config to specify number of rand_directed_instr_* passed in test plusargs
  int test_rand_directed_instr_stream_num = 1;

  rand int num_zfinx_reserved_reg;

  rand riscv_reg_t       zfinx_reserved_gpr[];

  rand bit ss_dbg_high_iteration_cnt;

  bit is_hwloop_test = 0;

  rand bit xpulp_instr_in_debug_rom;

  // Random rs1, rs3 for store instr
  rand riscv_reg_t  str_rs1;
  rand riscv_reg_t  str_rs3;

  // Enable debug trigger breakpoint setup in debug rom
  bit setup_debug_trigger_on_addr_match = 0;

  // Number of trigger iterations in a given test
  rand int trigger_iterations;

  // Random offset to program next trigger address
  rand int trigger_addr_offset;

  //random field to enable setting of single stepping only after
  //a trigger breakpoint causes debug entry
  rand bit debug_trigger_before_single_step;

  //random field to enable setting of single stepping only after
  //an ebreak causes debug entry
  rand bit debug_ebreak_before_single_step;

  // Config to insert random directed stream in debug program
  bit insert_rand_directed_instr_stream_in_debug_program = 0;

  // Config to insert interrupt handler to shift hwloop count by 1
  bit insert_handler_for_hwloop_count_range_test = 0;

  constraint ss_dbg_high_iteration_cnt_c {
    ss_dbg_high_iteration_cnt dist {0 := 60, 1 := 40};
  }

  // Override single step constraint
  constraint debug_single_step_c {
    solve ss_dbg_high_iteration_cnt before single_step_iterations;
    if (enable_debug_single_step & is_hwloop_test & ss_dbg_high_iteration_cnt) {
      single_step_iterations inside {[1000 : 5000]};
    }
    else if (enable_debug_single_step) {
      single_step_iterations inside {[10 : 50]};
    }
  }

  constraint dp_c {
    // Debug pointer may not be the return address, stack pointer, nor thread pointer
    if (!gen_debug_section) {
      dp == ZERO;
    } else {      
      !(dp inside {sp, tp, ra, scratch_reg, GP, RA, ZERO});
    }
  }

  constraint gpr_c {
    solve sp, tp, scratch_reg, dp, str_rs1, str_rs3 before gpr;
    foreach (gpr[i]) {
      !(gpr[i] inside {sp, tp, scratch_reg, pmp_reg, dp, str_rs1, str_rs3, ZERO, RA, GP});
    }
    unique {gpr};
  }

  // CV32E40P requires the MTVEC table to be aligned to 256KB boundaries
  constraint mtvec_c {
    tvec_alignment == 8;
  }

  // Constrain fast interrupt handler
  constraint knob_zero_fast_intr_dist_c {
    solve knob_zero_fast_intr_handlers before use_fast_intr_handler;
    knob_zero_fast_intr_handlers dist {
                                        0 :/ 8,
                                        1 :/ 2
                                      };
  }

  constraint fast_intr_handler_c {
    if (!enable_fast_interrupt_handler) {
      knob_zero_fast_intr_handlers == 1;
    }
    
    // Nver use fast handler for exceptions (interrupt 0)
    use_fast_intr_handler[0] == 0;

    knob_zero_fast_intr_handlers -> !use_fast_intr_handler;    

    // VECTORED mode required for any fast interrupts
    if (use_fast_intr_handler) {
      mtvec_mode == VECTORED;
    }
  }

  constraint num_zfinx_reserved_reg_c {
    if (RV32ZFINX inside {riscv_instr_pkg::supported_isa}) {
      num_zfinx_reserved_reg inside {[5:8]};
    } else {
      num_zfinx_reserved_reg == 0;
    }
  }

  constraint zfinx_reserved_gpr_c {
    solve num_zfinx_reserved_reg, dp, str_rs1, str_rs3 before zfinx_reserved_gpr;
    if (RV32ZFINX inside {riscv_instr_pkg::supported_isa}) {
      zfinx_reserved_gpr.size() == num_zfinx_reserved_reg;
      unique {zfinx_reserved_gpr};
      foreach(zfinx_reserved_gpr[i]) {
        !(zfinx_reserved_gpr[i] inside {ZERO, ra, sp, GP, tp, S0, S1, A0, A1, A2, A3, A4, A5});
        (zfinx_reserved_gpr[i] != dp);
        (zfinx_reserved_gpr[i] != str_rs1);
        (zfinx_reserved_gpr[i] != str_rs3);
      }

    } else {
      zfinx_reserved_gpr.size() == 0;
    }
  }

  constraint xpulp_instr_in_debug_rom_c {
    xpulp_instr_in_debug_rom dist {0 := 1, 1 := 2};
  }

  constraint str_rs1_rs3_c {
    solve dp before str_rs1, str_rs3;
    if(!no_load_store) {
      !(str_rs1 inside {sp, tp, ra, scratch_reg, GP, RA, ZERO, dp});
      str_rs1 inside {[S0:A5]}; // TODO: remove range constrained due to compressed stores
      !(str_rs3 inside {sp, tp, ra, scratch_reg, GP, RA, ZERO, dp});
      str_rs3 inside {[S0:A5]}; // TODO: remove range constrained due to compressed stores
      str_rs1 != str_rs3; //TODO : check if this can be removed
    } else {
      str_rs1 == ZERO;
      str_rs3 == ZERO;
    }
  }

  constraint trigger_c {
    trigger_iterations inside {[1:10]};
    trigger_addr_offset inside {[4:100]};
    trigger_addr_offset % 4 == 0;
  }

  `uvm_object_utils_begin(cv32e40p_instr_gen_config)
    `uvm_field_enum(mtvec_mode_t, mtvec_mode, UVM_DEFAULT)
    `uvm_field_int(knob_zero_fast_intr_handlers, UVM_DEFAULT)
    `uvm_field_enum(riscv_reg_t, dp, UVM_DEFAULT)
    `uvm_field_enum(riscv_reg_t, scratch_reg, UVM_DEFAULT)
    `uvm_field_sarray_enum(riscv_reg_t, gpr, UVM_DEFAULT)
    `uvm_field_int(enable_fast_interrupt_handler, UVM_DEFAULT)
    `uvm_field_int(use_fast_intr_handler, UVM_DEFAULT)
    `uvm_field_int(insert_rand_directed_instr_stream, UVM_DEFAULT)
    `uvm_field_int(test_rand_directed_instr_stream_num, UVM_DEFAULT)
    `uvm_field_int(num_zfinx_reserved_reg, UVM_DEFAULT)
    `uvm_field_array_enum(riscv_reg_t, zfinx_reserved_gpr, UVM_DEFAULT)
    `uvm_field_int(ss_dbg_high_iteration_cnt, UVM_DEFAULT)
    `uvm_field_int(is_hwloop_test, UVM_DEFAULT)
    `uvm_field_int(xpulp_instr_in_debug_rom, UVM_DEFAULT)
    `uvm_field_enum(riscv_reg_t, str_rs1, UVM_DEFAULT)
    `uvm_field_enum(riscv_reg_t, str_rs3, UVM_DEFAULT)
    `uvm_field_int(setup_debug_trigger_on_addr_match, UVM_DEFAULT)
    `uvm_field_int(trigger_iterations, UVM_DEFAULT)
    `uvm_field_int(trigger_addr_offset, UVM_DEFAULT)
    `uvm_field_int(debug_trigger_before_single_step, UVM_DEFAULT)
    `uvm_field_int(debug_ebreak_before_single_step, UVM_DEFAULT)
    `uvm_field_int(insert_rand_directed_instr_stream_in_debug_program, UVM_DEFAULT)
    `uvm_field_int(insert_handler_for_hwloop_count_range_test, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name="");
    super.new(name);

    get_bool_arg_value("+enable_fast_interrupt_handler=", enable_fast_interrupt_handler);
    get_bool_arg_value("+insert_rand_directed_instr_stream=", insert_rand_directed_instr_stream);
    get_int_arg_value("+test_rand_directed_instr_stream_num=", test_rand_directed_instr_stream_num);
    get_bool_arg_value("+is_hwloop_test=", is_hwloop_test);
    get_bool_arg_value("+setup_debug_trigger_on_addr_match=", setup_debug_trigger_on_addr_match);
    get_bool_arg_value("+debug_trigger_before_single_step=", debug_trigger_before_single_step);
    get_bool_arg_value("+debug_ebreak_before_single_step=", debug_ebreak_before_single_step);
    get_bool_arg_value("+insert_rand_directed_instr_stream_in_debug_program=", insert_rand_directed_instr_stream_in_debug_program);
    get_bool_arg_value("+insert_handler_for_hwloop_count_range_test=", insert_handler_for_hwloop_count_range_test);

    if ($test$plusargs("debug_trigger_before_single_step")) debug_trigger_before_single_step.rand_mode(0);
    if ($test$plusargs("debug_ebreak_before_single_step")) debug_ebreak_before_single_step.rand_mode(0);

  endfunction : new

  function void post_randomize();
    super.post_randomize();

    // Add in the debug pointer to reserved registers if we are using it
    if (gen_debug_section) begin
      reserved_regs = {tp, sp, scratch_reg, dp};
    end else begin
      reserved_regs = {tp, sp, scratch_reg};
    end

    if (zfinx_reserved_gpr.size()!= 0)
      reserved_regs = {reserved_regs, zfinx_reserved_gpr};

    if (!no_load_store)
      reserved_regs = {reserved_regs, str_rs1, str_rs3};

    // In the debug ROM some combinations are not valid because they use the same register (dscratch0)
    if (gen_debug_section) begin
      if ((enable_ebreak_in_debug_rom || set_dcsr_ebreak) && 
           enable_debug_single_step) begin
        `uvm_fatal("CVINSTGENCFG", 
                   $sformatf("Illegal combination of debug plusargs: enable_ebreak_in_debug_rom = %0d, set_dcsr_ebreakl = %0d, enable_debug_single_step = %0d",
                             enable_ebreak_in_debug_rom, set_dcsr_ebreak, enable_debug_single_step))
      end
    end

  endfunction : post_randomize

endclass : cv32e40p_instr_gen_config
