/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
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

class cv32e40p_float_zfinx_base_instr_stream extends cv32e40p_base_instr_stream;

  // only used if not in Zfinx mode
  rand riscv_fpr_t avail_fp_regs[];
  rand riscv_fpr_t reserved_fd[];

  // only used as a shorthand for RV32ZFINX inside {riscv_instr_pkg::supported_isa}, and initialized in "new" method
  bit is_zfinx;

  int unsigned num_of_avail_regs;

  `uvm_object_utils(cv32e40p_float_zfinx_base_instr_stream)

  function new (string name="");
    super.new(name);
    if (! (riscv_instr_pkg::RV32ZFINX inside {riscv_instr_pkg::supported_isa}) && ! (riscv_instr_pkg::RV32F inside {riscv_instr_pkg::supported_isa}) ) begin
      `uvm_error("cv32e40p_float_zfinx_base_instr_stream", "RV32ZFINX and RV32F are not defined in the supported_isa array (riscv_core_settings.sv)")
    end
    is_zfinx = riscv_instr_pkg::RV32ZFINX inside {riscv_instr_pkg::supported_isa};
  endfunction : new

  function void pre_randomize();
    avail_regs = new[num_of_avail_regs];
    avail_fp_regs = new[num_of_avail_regs];
    super.pre_randomize();
  endfunction

  function void post_randomize();
    riscv_instr instr;
    randomize_avail_regs();
    if (is_zfinx) instr = get_zfinx_instr();
    else instr = get_float_instr();
    randomize_gpr(instr);
    instr_list.push_back(instr);

    super.post_randomize();
  endfunction

  virtual function void randomize_avail_regs();
    // randomize fpr is RV32F is used
    if(!is_zfinx) begin
      if(avail_fp_regs.size() > 0) begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(avail_fp_regs,
        unique{avail_fp_regs};
        avail_fp_regs[0] inside {[S0 : A5]};
        foreach(avail_fp_regs[i]) {
          !(avail_fp_regs[i] inside {cfg.reserved_regs, reserved_rd});
        },
        "Cannot randomize avail_regs")
      end
    end
    // for all other cases (Zfinx or F) randomize X-registers
    super.randomize_avail_regs();
  endfunction

  function void randomize_gpr(riscv_instr instr);
    super.randomize_gpr(instr);
  endfunction

  virtual function riscv_instr get_zfinx_instr();
      return riscv_instr::get_rand_instr(.include_group({RV32ZFINX}));
  endfunction

  virtual function riscv_instr get_float_instr();
    if (XLEN >= 64) begin
      return riscv_instr::get_rand_instr(.include_group({RV32F, RV64F}));
    end else begin
      return riscv_instr::get_rand_instr(.include_group({RV32F}));
    end
  endfunction

endclass

class cv32e40p_float_zfinx_multycycle_instr_stream extends cv32e40p_float_zfinx_base_instr_stream;
  `uvm_object_utils(cv32e40p_float_zfinx_multycycle_instr_stream)
  `uvm_object_new
endclass

class cv32e40p_float_zfinx_corner_stream extends cv32e40p_float_zfinx_base_instr_stream;
  `uvm_object_utils(cv32e40p_float_zfinx_corner_stream)
  `uvm_object_new
endclass

class cv32e40p_float_zfinx_div_sqrt_instr_stream extends cv32e40p_float_zfinx_base_instr_stream;
  `uvm_object_utils(cv32e40p_float_zfinx_div_sqrt_instr_stream)
  `uvm_object_new
endclass
