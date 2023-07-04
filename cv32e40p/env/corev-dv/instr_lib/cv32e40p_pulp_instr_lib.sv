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

class cv32e40p_base_pulp_instr_stream extends cv32e40p_base_instr_stream;
  `uvm_object_utils(cv32e40p_base_pulp_instr_stream)

  function new(string name = "");
    super.new(name);
  endfunction

  function void pre_randomize();
    avail_regs = new[num_of_avail_regs];
    super.pre_randomize();
  endfunction

  function void post_randomize();
    gen_xpulp_instr();
    super.post_randomize();
  endfunction

  virtual function void gen_xpulp_instr(riscv_instr_name_t base_instr_list[$] = {});
    riscv_instr     instr;
    cv32e40p_instr  cv32_instr;

    avail_regs = new[num_of_avail_regs];
    randomize_avail_regs();
    cv32_instr = cv32e40p_instr::get_xpulp_instr(.include_instr(base_instr_list));

    //randomize GPRs for each instruction
    randomize_cv32e40p_gpr(cv32_instr, avail_regs);

    //randomize immediates for each instruction
    randomize_cv32e40p_instr_imm(cv32_instr);

    instr_list.push_back(cv32_instr);

  endfunction

endclass


class cv32e40p_xpulp_sanity_stream_test extends cv32e40p_base_pulp_instr_stream;

  `uvm_object_utils(cv32e40p_xpulp_sanity_stream_test)

  function new(string name = "cv32e40p_xpulp_sanity_stream_test");
    super.new(name);
  endfunction : new

  function void post_randomize();
    riscv_instr_gen_config  cfg_handle;
    riscv_instr placeholder_ins = riscv_instr::type_id::create("dummy_ins");
    riscv_instr_name_t all_xpulp_instr[$] = {};

    uvm_config_db#(riscv_instr_gen_config)::get(null, "*", "instr_cfg", cfg_handle);
    placeholder_ins.create_instr_list(cfg_handle);

    all_xpulp_instr = placeholder_ins.instr_group[RV32X];

    if (all_xpulp_instr.size() == 0) begin
      `uvm_fatal(this.get_type_name(), "No instruction inside RV32X. Check that RV_DV_ISA is correctly set")
    end

    foreach (all_xpulp_instr[i]) begin
      if (all_xpulp_instr[i] inside { CV_BEQIMM, CV_BNEIMM, CV_START, CV_STARTI, CV_END, CV_ENDI, CV_COUNT, CV_COUNTI, CV_SETUP, CV_SETUPI, CV_ELW } ) continue;
      gen_xpulp_instr({all_xpulp_instr[i]});
    end
  endfunction : post_randomize

endclass : cv32e40p_xpulp_sanity_stream_test


//Class : cv32e40p_xpulp_rand_stream
//Random xpulp stream class for randomized pulp instr stream
//including all xpulp other than hwloop and other rv32imfc instructions.
//Randomized number of instructions, gprs and immediates.
class cv32e40p_xpulp_rand_stream extends cv32e40p_base_instr_stream;

  rand int unsigned         num_of_xpulp_instr;
  rand int unsigned         num_of_riscv_instr;
  rand int unsigned         num_of_avail_regs;
  rand riscv_reg_t          cv32e40p_avail_regs[];
  rand riscv_reg_t          cv32e40p_exclude_regs[];

  int unsigned              num_of_reserved_regs;
  riscv_reg_t               cv32e40p_reserved_regs[];

  riscv_instr_name_t        xpulp_exclude_instr[];
  riscv_instr_category_t    xpulp_include_category[];
  riscv_instr_name_t        riscv_exclude_instr[];
  riscv_instr_group_t       riscv_exclude_group[];
  riscv_instr               riscv_instr_list[];

  `uvm_object_utils_begin(cv32e40p_xpulp_rand_stream)
      `uvm_field_int(num_of_xpulp_instr, UVM_DEFAULT)
      `uvm_field_int(num_of_riscv_instr, UVM_DEFAULT)
      `uvm_field_int(num_of_avail_regs, UVM_DEFAULT)
      `uvm_field_int(num_of_reserved_regs, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_reg_t,cv32e40p_avail_regs, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_reg_t,cv32e40p_exclude_regs, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_reg_t,cv32e40p_reserved_regs, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_instr_name_t,xpulp_exclude_instr, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_instr_name_t,riscv_exclude_instr, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_instr_group_t,riscv_exclude_group, UVM_DEFAULT)
  `uvm_object_utils_end

  constraint x_inst_gen_c {
    soft num_of_xpulp_instr inside {[50:500]};
  }

  constraint rv_inst_gen_c {
    soft num_of_riscv_instr inside {[50:300]};
  }

  constraint avail_regs_pulp_instr_c {
    num_of_avail_regs inside {[8:25]};
    num_of_reserved_regs == 5;
  }

  constraint cv32e40p_avail_regs_c {
    solve num_of_avail_regs,num_of_reserved_regs before cv32e40p_exclude_regs;
    cv32e40p_avail_regs.size() == num_of_avail_regs;
    cv32e40p_exclude_regs.size() == (32-num_of_reserved_regs-num_of_avail_regs);
    unique {cv32e40p_exclude_regs};
    foreach(cv32e40p_exclude_regs[i]) {
      !(cv32e40p_exclude_regs[i] inside {cv32e40p_reserved_regs});
    }
  }

  function new(string name = "cv32e40p_xpulp_rand_stream");
    super.new(name);

    num_of_reserved_regs = 5;
    cv32e40p_reserved_regs = new[num_of_reserved_regs];
    cv32e40p_reserved_regs = {ZERO, RA, SP, GP, TP};

  endfunction : new

  function void pre_randomize();
    super.pre_randomize();
    //Exclude list for XPULP instruction generation part
    xpulp_exclude_instr = {  CV_BEQIMM, CV_BNEIMM,
                             CV_START, CV_STARTI, CV_END, CV_ENDI, CV_COUNT, CV_COUNTI, CV_SETUP, CV_SETUPI,
                             CV_ELW,
                             C_ADDI16SP };

    //Exclude list for all random instruction generation part
    riscv_exclude_instr = {  CV_BEQIMM, CV_BNEIMM,
                             CV_START, CV_STARTI, CV_END, CV_ENDI, CV_COUNT, CV_COUNTI, CV_SETUP, CV_SETUPI,
                             CV_ELW,
                             C_ADDI16SP,
                             WFI,
                             URET, SRET, MRET, DRET,
                             ECALL,
                             JALR, JAL, C_JR, C_JALR, C_J, C_JAL};

  endfunction : pre_randomize

  function void post_randomize();
    cv32e40p_exclude_regs = {cv32e40p_exclude_regs,cv32e40p_reserved_regs};
    this.print();
    insert_rand_xpulp_instr(.no_branch(cfg.no_branch_jump),
                            .no_compressed(cfg.disable_compressed_instr),
                            .no_fence(cfg.no_fence),
                            .no_floating_point_instr(!cfg.enable_floating_point));

    //super.post_randomize();
  endfunction : post_randomize

  virtual function insert_rand_xpulp_instr(bit no_branch=1,
                                           bit no_compressed=1,
                                           bit no_fence=1,
                                           bit no_floating_point_instr=0);

    riscv_instr         instr;
    cv32e40p_instr      cv32_instr;
    string              str;
    int                 i;

    //use cfg for ebreak
    if(cfg.no_ebreak)
        riscv_exclude_instr = {riscv_exclude_instr, EBREAK, C_EBREAK};

    if(no_branch)
        riscv_exclude_instr = {riscv_exclude_instr, BEQ, BNE, BLT, BGE, BLTU, BGEU, C_BEQZ, C_BNEZ};

    if(no_compressed)
        riscv_exclude_group = {riscv_exclude_group, RV32C};

    if(no_fence)
        riscv_exclude_instr = {riscv_exclude_instr, FENCE, FENCE_I};

    if(no_floating_point_instr)
        riscv_exclude_group = {riscv_exclude_group, RV32F, RV32ZFINX};

    `uvm_info("cv32e40p_xpulp_rand_stream",
               $sformatf("Number of XPULP instr to be generated = %0d",num_of_xpulp_instr),UVM_HIGH)

    //(1) Generate random xpulp instructions
    i = 0;
    while (i < num_of_xpulp_instr) begin
      //Create and Randomize array for avail_regs each time to ensure randomization
      //To resolve the randomization issue within the same stream need this step
      cv32e40p_avail_regs = new[num_of_avail_regs];
      std::randomize(cv32e40p_avail_regs) with {  foreach(cv32e40p_avail_regs[i]) {
                                                    !(cv32e40p_avail_regs[i] inside {cv32e40p_exclude_regs});
                                                  }
                                               };

      cv32_instr = cv32e40p_instr::type_id::create($sformatf("cv32_instr_%0d", i));
      cv32_instr = cv32e40p_instr::get_xpulp_instr(.exclude_instr(xpulp_exclude_instr),
                                                   .include_category(xpulp_include_category));

      //randomize GPRs for each instruction
      randomize_cv32e40p_gpr(cv32_instr, cv32e40p_avail_regs);

      //randomize immediates for each instruction
      randomize_cv32e40p_instr_imm(cv32_instr);

      instr_list.push_back(cv32_instr);
      i++;

    end // while num_of_xpulp_instr

    //(2) Generate all random instructions
    riscv_instr_list = new[num_of_riscv_instr];
    for (i = 0; i < num_of_riscv_instr; i++) begin

      //Create and Randomize array for avail_regs each time to ensure randomization
      avail_regs = new[num_of_avail_regs];
      randomize_avail_regs();

      //Dont include RV32X instr here again
      riscv_exclude_group = {riscv_exclude_group, RV32X};

      riscv_instr_list[i] = riscv_instr::type_id::create($sformatf("riscv_instr_list_%0d", i));

      //exclude pulp instructions here
      riscv_instr_list[i] = riscv_instr::get_rand_instr(.exclude_instr(riscv_exclude_instr),
                                                        .exclude_group(riscv_exclude_group));

      //randomize GPRs for each instruction
      randomize_gpr(riscv_instr_list[i]);

      //randomize immediates for each instruction
      randomize_riscv_instr_imm(riscv_instr_list[i]);

    end // num_of_riscv_instr

    //mix steams for randomization
    mix_instr_stream(riscv_instr_list);

  endfunction

endclass : cv32e40p_xpulp_rand_stream

//Class : cv32e40p_xpulp_short_rand_stream
//extended from cv32e40p_xpulp_rand_stream
//Only override the constraints to reduced generated num of pulp instr
class cv32e40p_xpulp_short_rand_stream extends cv32e40p_xpulp_rand_stream;

  `uvm_object_utils(cv32e40p_xpulp_short_rand_stream)

  constraint x_inst_gen_c {
    num_of_xpulp_instr inside {[5:20]};
  }

  constraint rv_inst_gen_c {
    num_of_riscv_instr inside {[10:30]};
  }

  function new(string name = "cv32e40p_xpulp_short_rand_stream");
    super.new(name);
  endfunction : new

  function void post_randomize();
    super.post_randomize();
  endfunction : post_randomize

endclass : cv32e40p_xpulp_short_rand_stream

//Class : cv32e40p_xpulp_simd_stream_test
//extended from cv32e40p_xpulp_rand_stream
//Generate only PULP-SIMD instr from pulp instr group
class cv32e40p_xpulp_simd_stream_test extends cv32e40p_xpulp_rand_stream;
  `uvm_object_utils(cv32e40p_xpulp_simd_stream_test)

  constraint x_inst_gen_c {
    num_of_xpulp_instr inside {[50:300]};
  }

  constraint rv_inst_gen_c {
    num_of_riscv_instr inside {[10:150]};
  }

  function new(string name = "cv32e40p_xpulp_simd_stream_test");
    super.new(name);
  endfunction : new

  function void post_randomize();
    xpulp_include_category = {SIMD};
    super.post_randomize();
  endfunction : post_randomize

endclass : cv32e40p_xpulp_simd_stream_test

//Class : cv32e40p_xpulp_mac_stream_test
//extended from cv32e40p_xpulp_rand_stream
//Generate only PULP-MAC instr from pulp instr group
class cv32e40p_xpulp_mac_stream_test extends cv32e40p_xpulp_rand_stream;
  `uvm_object_utils(cv32e40p_xpulp_mac_stream_test)

  constraint x_inst_gen_c {
    num_of_xpulp_instr inside {[30:100]};
  }

  constraint rv_inst_gen_c {
    num_of_riscv_instr inside {[10:100]};
  }

  function new(string name = "cv32e40p_xpulp_mac_stream_test");
    super.new(name);
  endfunction : new

  function void post_randomize();
    xpulp_include_category = {MAC};
    super.post_randomize();
  endfunction : post_randomize

endclass : cv32e40p_xpulp_mac_stream_test
