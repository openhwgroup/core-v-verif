/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
 * Copyright 2023 Dolphin Design
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

// base class for pulp instruction
class cv32e40p_pulp_base_instr_stream extends cv32e40p_base_instr_stream;

  // exclude non-pulp instructions from generated in directed instr
  `define PULP_BASE_STREAM_EXCLUDE_LIST   {JAL, JALR, BEQ, BNE, BLT, BGE, BLTU, BGEU, ECALL, EBREAK, \
                                           DRET, MRET, URET, SRET, WFI, C_EBREAK, C_BEQZ, C_BNEZ, C_J, C_JAL, \
                                           C_JR, C_JALR, SB, SH, SW, C_SW, C_SWSP, FSW \
                                          }
  `define RV32C_INSTR_USE_SP_LIST         {C_LWSP, C_SWSP, C_ADDI4SPN, C_ADDI16SP}

  // properties - start
  string                  _header;
  riscv_instr_name_t      include_instr[]; 
  riscv_instr_name_t      exclude_instr[] = `PULP_BASE_STREAM_EXCLUDE_LIST;
  riscv_instr_category_t  include_category[], exclude_category[];
  riscv_instr_group_t     include_group[],    exclude_group[];
  int unsigned            num_of_avail_regs_gpr, num_of_avail_regs_rv32c;
  bit                     more_xpulp_instr;
  bit                     is_rv32f = riscv_instr_pkg::RV32F     inside {riscv_instr_pkg::supported_isa};
  bit                     is_zfinx = riscv_instr_pkg::RV32ZFINX inside {riscv_instr_pkg::supported_isa};

  rand int unsigned       num_of_instr_per_stream;
  rand bit                use_same_reglist_per_instr;         // use same reglist for directed instrs per stream
  rand bit                use_rand_fields_per_instr;          // workaround on vsim issue: same instr per stream has same fields value
  rand bit                use_pulp_only_for_directed_instr;   // use pulp instr only as directed instrs per stream
  rand bit                use_no_repetitive_instr_per_stream; // directed instr is not allow to repeat in a stream
  rand riscv_reg_t        avail_regs_gpr[];
  rand riscv_reg_t        avail_regs_rv32c[];
  // properties - end

  `uvm_object_utils(cv32e40p_pulp_base_instr_stream)

  // constraints - start
  constraint c_others {
    if (!use_no_repetitive_instr_per_stream) {
      soft num_of_instr_per_stream          == 50;
    } 
    soft use_same_reglist_per_instr         == 0;
    soft use_rand_fields_per_instr          == 1;
    soft use_pulp_only_for_directed_instr   == 0;
    soft use_no_repetitive_instr_per_stream == 0;
    solve use_no_repetitive_instr_per_stream before num_of_instr_per_stream;
  }
  // constraints - end

  function new(string name = "");
    super.new(name);
    _header = this.type_name;
    assert(!(is_rv32f && is_zfinx));
  endfunction

  function void pre_randomize();
    super.pre_randomize();
    // use_pulp_only_for_directed_instr.rand_mode(0);
    // use_no_repetitive_instr_per_stream.rand_mode(0);
    num_of_avail_regs_gpr   = XLEN - cfg.reserved_regs.size() + reserved_rd.size();
    num_of_avail_regs_rv32c = 8 - cfg.reserved_regs.size() + reserved_rd.size(); // 8 common regs
  endfunction : pre_randomize

  function void post_randomize();

    print_stream_setting();
    avail_regs_gpr    = new[num_of_avail_regs_gpr];
    if (num_of_avail_regs_rv32c < 9) avail_regs_rv32c = new[num_of_avail_regs_rv32c];
    else                             avail_regs_rv32c = new[8];

    if (use_same_reglist_per_instr) randomize_avail_regs();
    for (int i=0; i<num_of_instr_per_stream; i++) begin : GEN_DIRECTED_INSTR
      gen_directed_instr(.idx(i));
    end
    super.post_randomize();

  endfunction : post_randomize

  virtual function void print_stream_setting();
    `uvm_info(_header, $sformatf(">>%s with base constraints \
      \n>> num_of_instr_per_stream            [%0d] \
      \n>> use_same_reglist_per_instr         [%0b] \
      \n>> use_rand_fields_per_instr          [%0b] \
      \n>> use_pulp_only_for_directed_instr   [%0b] \
      \n>> use_no_repetitive_instr_per_stream [%0b] \
      ",
      get_name(), num_of_instr_per_stream, use_same_reglist_per_instr, use_rand_fields_per_instr,
      use_pulp_only_for_directed_instr, use_no_repetitive_instr_per_stream
      ), UVM_NONE);
  endfunction : print_stream_setting

  virtual function void gen_directed_instr(riscv_instr_name_t base_instr_list[$] = {}, int idx=0);
    riscv_instr     instr;
    cv32e40p_instr  instr_xpulp;
    update_current_instr_arg_list(idx);
    instr = new riscv_instr::get_rand_instr(
      .include_instr(include_instr),
      .exclude_instr(exclude_instr),
      .include_category(include_category),
      .exclude_category(exclude_category),
      .include_group(include_group),
      .exclude_group(exclude_group)
    );
    update_next_instr_arg_list(instr, idx);
    if (!use_same_reglist_per_instr) randomize_avail_regs();
    case (instr.group)
      RV32X : begin
                `DV_CHECK_FATAL($cast(instr_xpulp, instr), "Cast to instr_xpulp failed!");
                randomize_cv32e40p_gpr(instr_xpulp, avail_regs_gpr);
                randomize_cv32e40p_instr_imm(instr_xpulp);
              end
      RV32C:  begin 
                if (instr.instr_name inside `RV32C_INSTR_USE_SP_LIST) begin : C_INSTR_NEEDS_SP_REG
                  if (!(SP inside {avail_regs_rv32c}))
                    avail_regs_rv32c = new[avail_regs_rv32c.size() + 1] ({avail_regs_rv32c, SP});
                end else begin
                  if (SP inside {avail_regs_rv32c})
                    avail_regs_rv32c = new[avail_regs_rv32c.size() - 1] ({avail_regs_rv32c});
                end
                randomize_gpr(instr, avail_regs_rv32c); 
              end
      default: begin randomize_gpr(instr, avail_regs_gpr); end // todo: fp need more edit here?
    endcase
    if (instr.group == RV32X) begin
      modify_instr_fields(instr_xpulp); instr_list.push_back(instr_xpulp); 
    end else begin
      modify_instr_fields(instr);       instr_list.push_back(instr); 
    end
  endfunction : gen_directed_instr

  virtual function void randomize_avail_regs();
    if(avail_regs_gpr.size() > 0) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(avail_regs_gpr,
                                         unique{avail_regs_gpr};
                                         foreach(avail_regs_gpr[i]) {
                                           !(avail_regs_gpr[i] inside {cfg.reserved_regs, reserved_rd});
                                         },
                                         "Cannot randomize avail_regs_gpr")
    end
    if(avail_regs_rv32c.size() > 0) begin
      if (SP inside {avail_regs_rv32c}) 
        avail_regs_rv32c = new[avail_regs_rv32c.size() - 1] ({avail_regs_rv32c});
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(avail_regs_rv32c,
                                         unique{avail_regs_rv32c};
                                         foreach(avail_regs_rv32c[i]) {
                                           avail_regs_rv32c[i] inside {[S0:A5]};
                                           !(avail_regs_rv32c[i] inside {cfg.reserved_regs, reserved_rd});
                                         },
                                         "Cannot randomize avail_regs_rv32c")
    end
  endfunction : randomize_avail_regs

  function void randomize_gpr(riscv_instr instr, riscv_reg_t avail_regs[]={});
    assert(avail_regs.size() > 0);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      if (avail_regs.size() > 0) {
        if (has_rs1) { rs1 inside {avail_regs};}
        if (has_rs2) { rs2 inside {avail_regs};}
        if (has_rd)  { rd  inside {avail_regs};}
      }
      foreach (reserved_rd[i]) {
        if (has_rd) { rd != reserved_rd[i];}
        if (format == CB_FORMAT) { rs1 != reserved_rd[i];}
      }
      foreach (cfg.reserved_regs[i]) {
        if (has_rd) { rd != cfg.reserved_regs[i];}
        if (format == CB_FORMAT) { rs1 != cfg.reserved_regs[i];}
      }
    )
  endfunction : randomize_gpr

  virtual function void update_current_instr_arg_list(int idx=0);
    bit rand_status = std::randomize(more_xpulp_instr) with {more_xpulp_instr dist {1:=2, 0:=1};};
    assert(rand_status);
    if (more_xpulp_instr || use_pulp_only_for_directed_instr) begin
      include_group = new[1] ({RV32X});
      `ifndef CLUSTER
      if (!(CV_ELW inside {exclude_instr})) exclude_instr = new[exclude_instr.size() + 1] ({exclude_instr, CV_ELW});
      `endif
    end else begin
      include_group = new[3] ({RV32I, RV32M, RV32C}); // todo: fp need more edit here?
      if (is_rv32f && !(RV32F inside {include_group}))     include_group = new[include_group.size() + 1] ({include_group, RV32F});
      if (is_zfinx && !(RV32ZFINX inside {include_group})) include_group = new[include_group.size() + 1] ({include_group, RV32ZFINX});
    end
  endfunction : update_current_instr_arg_list

  virtual function void update_next_instr_arg_list(riscv_instr instr=null, int idx=0);
    assert(instr != null);
    if (use_no_repetitive_instr_per_stream) begin
      exclude_instr = new[exclude_instr.size() + 1] ({exclude_instr, instr.instr_name});
    end
  endfunction : update_next_instr_arg_list

  virtual function void modify_instr_fields(riscv_instr instr=null, int idx=0);
    riscv_reg_t t_avail_regs[$];
    // todo: fp need more edit here?
    if (instr.group == RV32C) t_avail_regs = avail_regs_rv32c;
    else                      t_avail_regs = avail_regs_gpr;
    t_avail_regs.shuffle();
    if (
      use_rand_fields_per_instr && 
      !(instr.instr_name inside `RV32C_INSTR_USE_SP_LIST)
    ) begin
      bit field_is_unique = $urandom_range(1);
      bit [4:0] fields_flag = {1'b0, instr.has_rs2, instr.has_rs1, instr.has_rd};
      for (int j=0; j<3; j++) begin
        if (fields_flag[j]) begin
        case (j)
          0 : instr.rd  = (field_is_unique) ? t_avail_regs.pop_front() : t_avail_regs[$urandom_range(0,t_avail_regs.size()-1)];
          1 : instr.rs1 = (field_is_unique) ? t_avail_regs.pop_front() : t_avail_regs[$urandom_range(0,t_avail_regs.size()-1)];
          2 : instr.rs2 = (field_is_unique) ? t_avail_regs.pop_front() : t_avail_regs[$urandom_range(0,t_avail_regs.size()-1)];
        endcase
        end
      end
    end // use_rand_fields_per_instr
  endfunction : modify_instr_fields

endclass // cv32e40p_pulp_base_instr_stream

// extended xpulp sanity streams that cycle thorugh all rv32x instr 
// it excludes instr related to hwloop and elw; it only covers one of the 2 cv_<branch> instr (CV_BEQIMM or CV_BNEIMM)
class cv32e40p_xpulp_sanity_stream_test extends cv32e40p_pulp_base_instr_stream;

  `uvm_object_utils(cv32e40p_xpulp_sanity_stream_test)
  `uvm_object_new

  riscv_instr_name_t bypass_xpulp_instr_list[] = {CV_START, CV_STARTI, CV_END, CV_ENDI, CV_COUNT, CV_COUNTI, CV_SETUP, CV_SETUPI, CV_ELW};

  constraint ovr_c_others {
    use_same_reglist_per_instr == 0;
    use_pulp_only_for_directed_instr == 1;
    use_no_repetitive_instr_per_stream == 1;
    if (use_no_repetitive_instr_per_stream) {
      num_of_instr_per_stream == riscv_instr::instr_group[RV32X].size() - bypass_xpulp_instr_list.size() - 1;
    }
  }

  virtual function void update_current_instr_arg_list(int idx=0);
    super.update_current_instr_arg_list(idx);
    if (!(CV_BEQIMM inside {exclude_instr})) exclude_instr = new[exclude_instr.size() + 1] ({exclude_instr, CV_BEQIMM});
    if (!(CV_BNEIMM inside {exclude_instr})) exclude_instr = new[exclude_instr.size() + 1] ({exclude_instr, CV_BNEIMM});
    if (idx == num_of_instr_per_stream-1) begin : LAST_PULP_INSTR_IS_CV_BRANCH
      riscv_instr_name_t selected_cv_br = $urandom_range(1) ? CV_BEQIMM : CV_BNEIMM;
      riscv_instr_name_t q_exclude_instr[$];
      int q_idx_selected_cv_br[$] = exclude_instr.find_first_index with (item == selected_cv_br);
      int idx_selected_cv_br = q_idx_selected_cv_br[0];
      assert(q_idx_selected_cv_br.size() == 1);
      assert(idx_selected_cv_br != 0 && idx_selected_cv_br != idx);
      for (int j=0; j<exclude_instr.size(); j++) begin
        if (j != idx_selected_cv_br) q_exclude_instr.push_back(exclude_instr[j]);
      end
      exclude_instr = new[exclude_instr.size()-1] (q_exclude_instr);
    end // LAST_PULP_INSTR_IS_CV_BRANCH
  endfunction : update_current_instr_arg_list

  function void post_randomize();
    exclude_instr = new[exclude_instr.size() + bypass_xpulp_instr_list.size()] ({exclude_instr, bypass_xpulp_instr_list});
    super.post_randomize();
  endfunction : post_randomize

endclass : cv32e40p_xpulp_sanity_stream_test

// extended xpulp stream that focus on MAC instructions
class cv32e40p_xpulp_mac_instr_stream extends cv32e40p_pulp_base_instr_stream;

  `uvm_object_utils(cv32e40p_xpulp_mac_instr_stream)
  `uvm_object_new

  constraint c_others {
    use_same_reglist_per_instr == 1;
    use_rand_fields_per_instr  == 1;
    use_pulp_only_for_directed_instr   dist {0 := 2, 1 := 1};
    use_no_repetitive_instr_per_stream dist {0 := 2, 1 := 1};
    if (use_no_repetitive_instr_per_stream) {
      num_of_instr_per_stream == riscv_instr::instr_category[MAC].size();
    } else {
      num_of_instr_per_stream == 50;
    }
    solve use_no_repetitive_instr_per_stream before num_of_instr_per_stream;
  }

  function void pre_randomize();
    super.pre_randomize();
    num_of_avail_regs_gpr = 4; // limit to 4 only registers: for rd, rs1, rs2 and +1 extra
  endfunction : pre_randomize

  virtual function void update_current_instr_arg_list(int idx=0);
    super.update_current_instr_arg_list(idx);
    if (more_xpulp_instr || use_pulp_only_for_directed_instr) begin
      include_group.delete();
      include_category = new[1] ({MAC});
    end
    else include_category.delete();
  endfunction : update_current_instr_arg_list

endclass : cv32e40p_xpulp_mac_instr_stream

// extended xpulp stream that focus on SMID instructions
class cv32e40p_xpulp_simd_instr_stream extends cv32e40p_pulp_base_instr_stream;

  `uvm_object_utils(cv32e40p_xpulp_simd_instr_stream)
  `uvm_object_new

  constraint c_others {
    use_same_reglist_per_instr == 1;
    use_rand_fields_per_instr  == 1;
    use_pulp_only_for_directed_instr   dist {0 := 2, 1 := 1};
    use_no_repetitive_instr_per_stream dist {0 := 2, 1 := 1};
    if (use_no_repetitive_instr_per_stream && use_pulp_only_for_directed_instr) {
      num_of_instr_per_stream == riscv_instr::instr_category[SIMD].size();
    } else {
      num_of_instr_per_stream == 50;
    }
    solve use_pulp_only_for_directed_instr   before use_no_repetitive_instr_per_stream;
    solve use_no_repetitive_instr_per_stream before num_of_instr_per_stream;
  }

  function void pre_randomize();
    super.pre_randomize();
    num_of_avail_regs_gpr = 4; // limit to 4 only registers: for rd, rs1, rs2 and +1 extra
  endfunction : pre_randomize

  virtual function void update_current_instr_arg_list(int idx=0);
    super.update_current_instr_arg_list(idx);
    if (more_xpulp_instr || use_pulp_only_for_directed_instr) begin
      include_group.delete();
      include_category = new[1] ({SIMD});
    end
    else include_category.delete();
  endfunction : update_current_instr_arg_list

endclass : cv32e40p_xpulp_simd_instr_stream

//Class : cv32e40p_xpulp_rand_stream
//Random xpulp stream class for randomized pulp instr stream
//including all xpulp other than hwloop and other rv32imfc instructions.
//Randomized number of instructions, gprs and immediates.
class cv32e40p_xpulp_rand_stream extends cv32e40p_base_instr_stream;

  rand int unsigned     num_of_xpulp_instr;
  rand int unsigned     num_of_riscv_instr;
  rand int unsigned     num_of_avail_regs;
  rand riscv_reg_t      cv32e40p_avail_regs[];

  riscv_instr_name_t    xpulp_exclude_instr[];
  riscv_instr_name_t    riscv_exclude_instr[];
  riscv_instr_group_t   riscv_exclude_group[];
  riscv_instr           riscv_instr_list[];

  `uvm_object_utils(cv32e40p_xpulp_rand_stream)

  constraint x_inst_gen_c {
    soft num_of_xpulp_instr inside {[50:300]};
  }

  constraint rv_inst_gen_c {
    soft num_of_riscv_instr inside {[50:300]};
  }

  constraint avail_regs_pulp_instr_c {
    num_of_avail_regs inside {[8:26]};
  }

  constraint cv32e40p_avail_regs_c {
    solve num_of_avail_regs before cv32e40p_avail_regs;
    cv32e40p_avail_regs.size() == num_of_avail_regs;
    unique {cv32e40p_avail_regs};
    foreach(cv32e40p_avail_regs[i]) {
      !(cv32e40p_avail_regs[i] inside {ZERO, RA, SP, GP, TP});
    }
  }

  function new(string name = "cv32e40p_xpulp_rand_stream");
    super.new(name);
  endfunction : new

  function void pre_randomize();
    super.pre_randomize();
  endfunction : pre_randomize

  function void post_randomize();
    insert_rand_xpulp_instr();
    //super.post_randomize();
  endfunction : post_randomize

  virtual function insert_rand_xpulp_instr();
    riscv_instr         instr;
    cv32e40p_instr      cv32_instr;
    string              str;
    int                 i;

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
                             URET, SRET, MRET,
                             ECALL,
                             JALR, JAL, C_JR, C_JALR, C_J, C_JAL};

    //use cfg for ebreak
    if(cfg.no_ebreak)
        riscv_exclude_instr = {riscv_exclude_instr, EBREAK, C_EBREAK};

    `uvm_info("cv32e40p_xpulp_rand_stream", $sformatf("Number of XPULP instr to be generated =  %0d",num_of_xpulp_instr), UVM_HIGH);

    //(1) Generate random xpulp instructions
    for (i = 0; i < num_of_xpulp_instr; i++) begin
      //Create and Randomize array for avail_regs each time to ensure randomization
      //To resolve the randomization issue within the same stream need this step
      cv32e40p_avail_regs = new[num_of_avail_regs];
      std::randomize(cv32e40p_avail_regs) with  {   unique {cv32e40p_avail_regs};
                                                    foreach(cv32e40p_avail_regs[i]) {
                                                        !(cv32e40p_avail_regs[i] inside {ZERO, RA, SP, GP, TP});
                                                    }
                                                };

      cv32_instr = cv32e40p_instr::type_id::create($sformatf("cv32_instr_%0d", i));
      cv32_instr = cv32e40p_instr::get_xpulp_instr(.exclude_instr(xpulp_exclude_instr));

      //randomize GPRs for each instruction
      randomize_cv32e40p_gpr(cv32_instr, cv32e40p_avail_regs);

      //randomize immediates for each instruction
      randomize_cv32e40p_instr_imm(cv32_instr);

      instr_list.push_back(cv32_instr);

    end // num_of_xpulp_instr

    //(2) Generate all random instructions
    riscv_instr_list = new[num_of_riscv_instr];
    for (i = 0; i < num_of_riscv_instr; i++) begin

      //Create and Randomize array for avail_regs each time to ensure randomization
      avail_regs = new[num_of_avail_regs];
      randomize_avail_regs();

      riscv_instr_list[i] = riscv_instr::type_id::create($sformatf("riscv_instr_list_%0d", i));
      riscv_instr_list[i] = riscv_instr::get_rand_instr(.exclude_instr(riscv_exclude_instr)); //FIXME: reduce frequency of pulp instructions

      //randomize GPRs for each instruction
      randomize_gpr(riscv_instr_list[i]);

      //randomize immediates for each instruction
      randomize_riscv_instr_imm(riscv_instr_list[i]);

    end // num_of_riscv_instr

    //mix steams for randomization
    mix_instr_stream(riscv_instr_list);

  endfunction

endclass : cv32e40p_xpulp_rand_stream

class cv32e40p_xpulp_short_rand_stream extends cv32e40p_xpulp_rand_stream;

  `uvm_object_utils(cv32e40p_xpulp_short_rand_stream)

  constraint x_inst_gen_c {
    soft num_of_xpulp_instr inside {[5:20]};
  }

  constraint rv_inst_gen_c {
    soft num_of_riscv_instr inside {[10:30]};
  }

  function new(string name = "cv32e40p_xpulp_short_rand_stream");
    super.new(name);
  endfunction : new

  function void post_randomize();
    super.post_randomize();
  endfunction : post_randomize

endclass : cv32e40p_xpulp_short_rand_stream

