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

  riscv_instr_name_t        xpulp_exclude_instr[];
  riscv_instr_category_t    xpulp_include_category[];
  riscv_instr_name_t        riscv_exclude_common_instr[];
  riscv_instr_name_t        riscv_exclude_instr[];
  riscv_instr_group_t       riscv_exclude_group[];

  int unsigned              num_zfinx_gpr;
  int unsigned              num_str_reserved_gpr;
  riscv_reg_t               cv32e40p_zfinx_regs[];

  `uvm_object_utils_begin(cv32e40p_xpulp_rand_stream)
      `uvm_field_int(num_of_xpulp_instr, UVM_DEFAULT)
      `uvm_field_int(num_of_riscv_instr, UVM_DEFAULT)
      `uvm_field_int(num_of_avail_regs, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_reg_t,cv32e40p_avail_regs, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_reg_t,cv32e40p_exclude_regs, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_instr_name_t,xpulp_exclude_instr, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_instr_name_t,riscv_exclude_common_instr, UVM_DEFAULT)
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
    if ((cfg.enable_fp_in_x_regs == 1) && (RV32ZFINX inside {riscv_instr_pkg::supported_isa})) {
      num_of_avail_regs  >= 8;
      num_of_avail_regs  <= (24 - num_zfinx_gpr - num_str_reserved_gpr);
    } else {
      num_of_avail_regs  >= 8;
      num_of_avail_regs  <= (24 - num_str_reserved_gpr);
    }
  }

  constraint cv32e40p_avail_regs_c {
    solve num_of_avail_regs before cv32e40p_exclude_regs;
    cv32e40p_avail_regs.size() == num_of_avail_regs;
    cv32e40p_exclude_regs.size() == (32 - num_of_avail_regs - cfg.reserved_regs.size());
    unique {cv32e40p_exclude_regs};
    foreach(cv32e40p_exclude_regs[i]) {
      !(cv32e40p_exclude_regs[i] inside {cfg.reserved_regs});
    }
  }

  function new(string name = "cv32e40p_xpulp_rand_stream");
    super.new(name);

  endfunction : new

  function void pre_randomize();
    super.pre_randomize();
    uvm_default_printer.knobs.begin_elements = -1;
    //Exclude list for XPULP instruction generation part
    xpulp_exclude_instr = {  CV_START, CV_STARTI, CV_END, CV_ENDI, CV_COUNT, CV_COUNTI, CV_SETUP, CV_SETUPI,
                             CV_ELW,
                             C_ADDI16SP };

    //Exclude list for all random instruction generation part
    riscv_exclude_common_instr = { CV_START, CV_STARTI, CV_END, CV_ENDI, CV_COUNT, CV_COUNTI, CV_SETUP, CV_SETUPI,
                                   CV_ELW,
                                   C_ADDI16SP,
                                   WFI,
                                   URET, SRET, MRET, DRET,
                                   ECALL,
                                   JALR, JAL, C_JR, C_JALR, C_J, C_JAL };

    num_zfinx_gpr = cv32e40p_cfg.num_zfinx_reserved_reg;
    cv32e40p_zfinx_regs = new[num_zfinx_gpr];
    cv32e40p_zfinx_regs = cv32e40p_cfg.zfinx_reserved_gpr;
    num_str_reserved_gpr = (!cv32e40p_cfg.no_load_store) ? 2 : 0; // TODO: add more randomization

  endfunction : pre_randomize

  function void post_randomize();
    cv32e40p_exclude_regs = {cv32e40p_exclude_regs,cfg.reserved_regs};
    cv32e40p_exclude_regs.sort();

    if((cv32e40p_exclude_regs.size() < 2) || (cv32e40p_exclude_regs.size() > 25))
      `uvm_fatal(this.get_type_name(), "cv32e40p_exclude_regs out of range")

    this.print();
    insert_rand_xpulp_instr(.no_branch(cfg.no_branch_jump),
                            .no_compressed(cfg.disable_compressed_instr),
                            .no_fence(cfg.no_fence),
                            .no_floating_point_instr(~(cfg.enable_floating_point | cfg.enable_fp_in_x_regs)));

    //super.post_randomize();
  endfunction : post_randomize

  virtual function insert_rand_xpulp_instr(bit no_branch=1,
                                           bit no_compressed=1,
                                           bit no_fence=1,
                                           bit no_floating_point_instr=0);

    riscv_instr                 instr;
    cv32e40p_instr              cv32_instr;
    riscv_fp_in_x_regs_instr    zfinx_instr;
    string                      str;
    int                         i;
    riscv_instr_group_t         riscv_exclude_xpulp[];
    int                         rv32_ins, pulp_ins;

    riscv_exclude_instr = {riscv_exclude_common_instr};

    //use cfg for ebreak
    if(cfg.no_ebreak)
        riscv_exclude_instr = {riscv_exclude_instr, EBREAK, C_EBREAK};

    if(no_branch)
        riscv_exclude_instr = {riscv_exclude_instr, BEQ, BNE, BLT, BGE, BLTU, BGEU, C_BEQZ, C_BNEZ, CV_BEQIMM, CV_BNEIMM};

    if(no_compressed)
        riscv_exclude_group = {riscv_exclude_group, RV32C, RV32FC};

    if(no_fence)
        riscv_exclude_instr = {riscv_exclude_instr, FENCE, FENCE_I};

    if(no_floating_point_instr)
        riscv_exclude_group = {riscv_exclude_group, RV32F, RV32ZFINX};

    if(cfg.sp != SP) begin // prevent corruption due to sw(sp)
      riscv_exclude_instr = {riscv_exclude_instr, C_SWSP, C_FSWSP};
    end

    `uvm_info("cv32e40p_xpulp_rand_stream",
               $sformatf("Total XPULP+RISCV instr gen in test %0d + %0d",num_of_xpulp_instr,num_of_riscv_instr),UVM_HIGH)

    //Exclude RV32X instr for riscv_exclude_xpulp
    riscv_exclude_xpulp = {riscv_exclude_group, RV32X};
    rv32_ins = num_of_riscv_instr;
    pulp_ins = num_of_xpulp_instr;

    i = 0;
    while (i < (num_of_xpulp_instr+num_of_riscv_instr)) begin

      randcase
        pulp_ins:
          begin
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
          end
        rv32_ins:
          begin
            //Create and Randomize array for avail_regs each time to ensure randomization
            avail_regs = new[num_of_avail_regs];
            randomize_avail_regs();

            instr = riscv_instr::type_id::create($sformatf("riscv_instr_%0d", i));

            //exclude pulp instructions here
            instr = riscv_instr::get_rand_instr(.exclude_instr(riscv_exclude_instr),
                                                .exclude_group(riscv_exclude_xpulp));

            //randomize immediates for each instruction
            randomize_riscv_instr_imm(instr);

            //randomize GPRs for each instruction
            if(instr.group != RV32ZFINX) begin
              randomize_gpr(instr);
              store_instr_gpr_handling(instr);
              instr_list.push_back(instr);
            end else begin
              zfinx_instr = riscv_fp_in_x_regs_instr::type_id::create($sformatf("zfinx_instr_%0d", i));
              `DV_CHECK_FATAL($cast(zfinx_instr, instr), "Cast to zfinx instruction type failed!");
              randomize_zfinx_gpr(zfinx_instr, cv32e40p_zfinx_regs);
              instr_list.push_back(zfinx_instr);
            end

          end
      endcase
      instr_list[$].comment = {$sformatf(" Inserted %0s - idx[%0d]", get_name(), i)};

      i++;

    end // while

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

// Class : cv32e40p_xpulp_with_priv_instr
// extended from cv32e40p_xpulp_rand_stream
// Generate Random pulp instr mixed with m-mode priv instr such as WFI, ECALL,
// EBREAK etc. The test must be run with random interrupt traffic to ensure WFI
// does not cause a test stall
class cv32e40p_xpulp_with_priv_instr extends cv32e40p_xpulp_rand_stream;
  `uvm_object_utils_begin(cv32e40p_xpulp_with_priv_instr)
      `uvm_field_int(num_of_xpulp_instr, UVM_DEFAULT)
      `uvm_field_int(num_of_riscv_instr, UVM_DEFAULT)
      `uvm_field_int(num_of_avail_regs, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_reg_t,cv32e40p_avail_regs, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_reg_t,cv32e40p_exclude_regs, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_instr_name_t,xpulp_exclude_instr, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_instr_name_t,riscv_exclude_common_instr, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_instr_name_t,riscv_exclude_instr, UVM_DEFAULT)
      `uvm_field_sarray_enum(riscv_instr_group_t,riscv_exclude_group, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "cv32e40p_xpulp_with_priv_instr");
    super.new(name);
  endfunction : new

  function void post_randomize();
    riscv_exclude_common_instr = { CV_START, CV_STARTI, CV_END, CV_ENDI, CV_SETUP, CV_SETUPI,
                                   CV_ELW,
                                   C_ADDI16SP,
                                   URET, SRET, MRET, DRET,
                                   JALR, JAL, C_JR, C_JALR, C_J, C_JAL };
    super.post_randomize();
  endfunction : post_randomize

endclass : cv32e40p_xpulp_with_priv_instr
