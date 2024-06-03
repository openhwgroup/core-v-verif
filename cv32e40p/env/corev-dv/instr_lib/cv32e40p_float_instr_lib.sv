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

// [Dolphin Design updates]
// This file contains stream classes that use to generate single precision fp instructions

// ALL FP (SINGLE PERCISION) STREAM CLASSESS - start
  // base class for fp instruction stream generation
  // all the directed instrs generated in a stream are fp instr 

class cv32e40p_float_zfinx_base_instr_stream extends cv32e40p_base_instr_stream;

  localparam TOTAL_INSTR_F_TYPE     = 26;
  localparam TOTAL_INSTR_FC_TYPE    = 4;
  localparam TOTAL_INSTR_ZFINX_TYPE = 22;
  localparam MAX_D_REG              = 1; // rd/fd
  localparam MAX_S_REG              = 3; // rs/fs
  localparam TOTAL_D_AND_S_REG      = MAX_D_REG + MAX_S_REG;

  `include "instr_lib/cv32e40p_float_instr_lib_defines.sv"

  // properties - start
  string                      _header;
  cv32e40p_instr_gen_config   cfg_cv32e40p;
  bit                         is_zfinx = riscv_instr_pkg::RV32ZFINX inside {riscv_instr_pkg::supported_isa};
  bit                         is_fp_instr, is_fpc_instr;
  riscv_instr_name_t          include_instr[];
  riscv_instr_name_t          exclude_instr[];
  riscv_instr_category_t      include_category[];
  riscv_instr_category_t      exclude_category[];
  riscv_instr_group_t         include_group[];
  riscv_instr_group_t         exclude_group[];
  bit                         use_special_operand_patterns;       // use special pattern opeands on directed instrs
  bit                         use_fp_only_for_directed_instr;     // use fp instr only as directed instrs in stream
  bit                         use_no_repetitive_instr_per_stream; // directed instr is not allow to repeat in a stream
  bit                         use_same_instr_per_stream;          // same directed is use within a stream
  bit                         use_prev_rd_on_next_operands;       // previous instr rd is used for directed instr operands
  bit                         use_diff_regs_for_operands = 0;     // to control rand instr uses different registers for instr oeprands
  bit                         more_weight_for_fdiv_fsqrt_gen;     // more weight on generating fdiv and fsqrt directed_instr
  bit                         use_only_for_fdiv_fsqrt_gen;        // use only fdiv and fsqrt directed_instr
  bit                         init_gpr = (is_zfinx) ? 1 : 0;      // initialize gpr registers in stream with rand value
  bit                         init_fpr = (is_zfinx) ? 0 : 1;      // initialize fpr registers in stream with rand value
  bit                         en_clr_fflags_af_instr;             // clear fflag to prevent residual fflags status of current f_instr
  bit                         en_clr_fstate;                      // clean the fstate for current f_instr
  bit                         include_load_store_base_sp;         // include store instr that uses sp

    // for use_prev_rd_on_next_operands implementation usage - start
  riscv_reg_t                 prev_rd;
  riscv_fpr_t                 prev_fd;
  bit                         prev_has_rd_detected, prev_has_fd_detected;
  bit [TOTAL_D_AND_S_REG-1:0] prev_has_r_flags, prev_has_f_flags; // use to store prev instr has_* reg flags
  bit [TOTAL_D_AND_S_REG-1:0] curr_has_r_flags, curr_has_f_flags; // use to store curr instr has_* reg flags
    // for use_prev_rd_on_next_operands implementation usage - end

    // for clr_crs_fflags usage - start
  bit                 clr_csr_option = $urandom_range(1);
  bit                 clr_csr_init_done = 0; // reduce overhead
  riscv_instr_name_t  csr_name = INVALID_INSTR;
  logic [31:0]        csr_rm = $urandom_range(0,4);
  logic [31:0]        csr_mstatus_fs = 0;
    // for clr_crs_fflags usage - end

  rand int unsigned       num_of_instr_per_stream;
  rand riscv_reg_t        avail_gp_regs[][];        // regs for extension zfinx and f
  rand riscv_fpr_t        avail_fp_regs[][];        // regs for extension f only
  rand riscv_reg_t        gp_reg_scratch;           // allocation for scratch reg 
  rand riscv_reg_t        gp_reg_sp;                // allocation for store instr that uses sp
  rand bit [31:0]         imm;
  rand f_rounding_mode_t  rm;
  rand bit                use_rounding_mode_from_instr;
  rand bit                use_xpulp_as_others_instr;

  // rand bit                use_special_operand_patterns;
  rand operand_pattens_t  operand_a_pattern[];
  rand operand_pattens_t  operand_b_pattern[];
  rand operand_pattens_t  operand_c_pattern[];
  rand bit                sign_a[],     sign_b[],     sign_c[];
  rand bit [7:0]          exp_a[],      exp_b[],      exp_c[];
  rand bit [22:0]         mantissa_a[], mantissa_b[], mantissa_c[];
  rand bit [31:0]         operand_a[],  operand_b[],  operand_c[];
  // properties - end

  `uvm_object_utils(cv32e40p_float_zfinx_base_instr_stream)

  // constraints - start
  constraint c_others {
    if (use_no_repetitive_instr_per_stream) {
      if (is_zfinx) {soft num_of_instr_per_stream inside {[TOTAL_INSTR_ZFINX_TYPE/2 : TOTAL_INSTR_ZFINX_TYPE]};}
      else          {soft num_of_instr_per_stream inside {[(TOTAL_INSTR_F_TYPE+TOTAL_INSTR_FC_TYPE)/2 : (TOTAL_INSTR_F_TYPE+TOTAL_INSTR_FC_TYPE)]};}
    } else {
      if (en_clr_fflags_af_instr) {soft num_of_instr_per_stream == 50;}
      else                        {soft num_of_instr_per_stream == 100;}
    }
    num_of_instr_per_stream > 0;
  }

  constraint c_avail_gp_regs {
    soft avail_gp_regs.size() == num_of_instr_per_stream;
    foreach (avail_gp_regs[i]) {
      soft avail_gp_regs[i].size() == 10; // more buffer as some dedicated gpr should not been used
      unique{avail_gp_regs[i]};
      soft avail_gp_regs[i][0] inside {[S0:A5]}; // MUST: RV32C only uses 8 most common xregs
      soft avail_gp_regs[i][1] inside {SP};      // MUST: some random instr uses SP as rd
      foreach (avail_gp_regs[i][j]) {
        if (cfg.gen_debug_section) {
        !(avail_gp_regs[i][j] inside {cfg.reserved_regs, reserved_rd, gp_reg_scratch, gp_reg_sp, cfg_cv32e40p.dp});
        } else {
        !(avail_gp_regs[i][j] inside {cfg.reserved_regs, reserved_rd, gp_reg_scratch, gp_reg_sp});
        }
      }
    }
  }
  
  constraint c_gp_reg_scratch {
    !(gp_reg_scratch inside {cfg.reserved_regs, reserved_rd, ZERO, SP});
    solve gp_reg_scratch before avail_gp_regs;
  }

  constraint c_gp_reg_sp {
    soft gp_reg_sp == gp_reg_scratch;
    if (include_load_store_base_sp) {
      if (cv32e40p_cfg.sp != SP) {
        gp_reg_sp == SP; // reserve this for load-store-sp
      }
    }
    solve gp_reg_sp before avail_gp_regs;
  }

  constraint c_avail_fp_regs {
    soft avail_fp_regs.size() == num_of_instr_per_stream;
    foreach (avail_fp_regs[i]) {
      soft avail_fp_regs[i].size() > FLEN/2;   // widen the range of selections
      soft avail_fp_regs[i].size() < FLEN + 1; // total of available fpr
      unique{avail_fp_regs[i]};
      soft avail_fp_regs[i][0] inside {[FS0:FA5]}; // MUST: RV32CF only uses 8 most common fregs - fs
      soft avail_fp_regs[i][1] inside {[FS0:FA5]}; // MUST: RV32CF only uses 8 most common fregs - fd
    }
  }

  constraint c_use_xpulp_as_others_instr {
    use_xpulp_as_others_instr dist {0:=3, 1:=1};
  }

  `C_OPERAND_PATTERN(a)
  `C_OPERAND_PATTERN(b)
  `C_OPERAND_PATTERN(c)
  `C_OPERAND(a)
  `C_OPERAND(b)
  `C_OPERAND(c)
  // constraints - end

  function new (string name="cv32e40p_float_zfinx_base_instr_stream");
    super.new(name);
    _header = this.type_name;
    if ( !(riscv_instr_pkg::RV32ZFINX inside {riscv_instr_pkg::supported_isa}) && ! (riscv_instr_pkg::RV32F inside {riscv_instr_pkg::supported_isa}) ) begin
      `uvm_error(_header, $sformatf("RV32ZFINX and RV32F are not defined in RV_DV_ISA - refer cv32e40p_supported_isa.svh"));
    end
  endfunction: new

  function void pre_randomize();
    super.pre_randomize();
    use_special_operand_patterns        = 0;
    use_fp_only_for_directed_instr      = 1; // directed instr is fp only
    use_prev_rd_on_next_operands        = 0;
    use_no_repetitive_instr_per_stream  = 0;
    en_clr_fflags_af_instr              = 1;
    en_clr_fstate                       = 0;
    include_load_store_base_sp          = $urandom_range(1);
    if (cfg.gen_debug_section) begin
      if (!$cast(cfg_cv32e40p, cfg)) begin
        `uvm_fatal(_header, $sformatf("pre_randomize - cfg_cv32e40p casting failed"));
      end
    end
  endfunction: pre_randomize

  function void post_randomize();
    riscv_instr                 instr;
    riscv_fp_in_x_regs_instr    instr_zfinx;
    riscv_floating_point_instr  instr_f;

    print_stream_setting();
    initialize_regs();

    if (use_special_operand_patterns) begin
      foreach (operand_a[i]) begin
        `uvm_info(_header, $sformatf(">> Specific operand patterns \
          \n>> instr[%0d] operand_a is %0d [%s]\
          \n>> instr[%0d] operand_b is %0d [%s]\
          \n>> instr[%0d] operand_c is %0d [%s]\
          \n>>", 
          i, operand_a[i][31:12], operand_a_pattern[i],
          i, operand_b[i][31:12], operand_b_pattern[i],
          i, operand_c[i][31:12], operand_c_pattern[i]), UVM_DEBUG);
          // i, operand_c[i][31:12], operand_c_pattern[i]), (use_special_operand_patterns) ? UVM_NONE : UVM_DEBUG);
      end
    end

    for (int i = 0; i < num_of_instr_per_stream; i++) begin : GEN_N_MANIPULATE_INSTR

      // directed instr gen per stream generation
      update_current_instr_arg_list(i);
      instr = new riscv_instr::get_rand_instr(
        .include_instr(include_instr),
        .exclude_instr(exclude_instr),
        .include_category(include_category),
        .exclude_category(exclude_category),
        .include_group(include_group),
        .exclude_group(exclude_group)
      );
      is_fp_instr = (instr.group inside {RV32F, RV32ZFINX});
      update_next_instr_arg_list(instr, i);
      add_instr_prior_directed_instr(instr, i); 

      // directed instr randomization based on extension
      if (!is_fp_instr) begin : OTHER_NON_FP_SUPPORTED_EXTENSIONS
        randomize_gpr(instr);
        if (!(instr.group == RV32C || instr.group == RV32FC))
          f_use_prev_rd_on_next_operands(.p_instr((use_prev_rd_on_next_operands) ? instr : null), .idx(i));
        if (instr.instr_name inside {`STORE_INSTR_LIST, `FP_STORE_INSTR_LIST}) begin
          // wa_prevent_store_on_code_space(instr);
          store_instr_gpr_handling(instr);
        end
        instr_list.push_back(instr);
      end
      else if (is_zfinx) begin : EXTENSION_ZFINX
        `DV_CHECK_FATAL($cast(instr_zfinx, instr), $sformatf("Cast to instr_zfinx failed for %s!", instr.instr_name.name()) );
        randomize_gpr_zfinx(instr_zfinx, i);
        f_use_prev_rd_on_next_operands(.p_instr_zfinx((use_prev_rd_on_next_operands) ? instr_zfinx : null), .idx(i));
        if (use_special_operand_patterns)
          rand_fp_special_operands_zfinx(instr_zfinx, i);
        instr_list.push_back(instr_zfinx);
        `uvm_info(_header, $sformatf("\n>>>> instr_zfinx[%s] >>>> \
          \n>> has_rs1 | has_rs2 | has_rs3 | has_rd  | has_imm    -> %0b , %0b , %0b , %0b , %0b \
          \n>> rs1     | rs2     | rs3     | rd      | imm        -> %s  , %s  , %s  , %s  , 8'h%8h \
          \n>>>>\n",
          instr_zfinx.instr_name.name(), 
          instr_zfinx.has_rs1,    instr_zfinx.has_rs2,    instr_zfinx.has_rs3,    instr_zfinx.has_rd,    instr_zfinx.has_imm,
          instr_zfinx.rs1.name(), instr_zfinx.rs2.name(), instr_zfinx.rs3.name(), instr_zfinx.rd.name(), instr_zfinx.imm), UVM_DEBUG);
      end
      else begin : EXTENSION_F
        `DV_CHECK_FATAL($cast(instr_f, instr), $sformatf("Cast to instr_f failed for %s!", instr.instr_name.name()) );
        randomize_fpr(instr_f, i);
        f_use_prev_rd_on_next_operands(.p_instr_f((use_prev_rd_on_next_operands) ? instr_f : null), .idx(i));
        if (instr_f.instr_name inside {`FP_STORE_INSTR_LIST}) begin
          // wa_prevent_store_on_code_space(instr_f);
          store_instr_gpr_handling(instr);
        end
        if (use_special_operand_patterns)
          rand_fp_special_operands(instr_f, i);
        instr_list.push_back(instr_f);
        `uvm_info(_header, $sformatf("\n>>>> instr_f[%s] >>>> \
          \n>> has_rs1 | has_rs2 | has_rd  | has_imm    -> %0b , %0b , %0b , %0b \
          \n>> rs1     | rs2     | rd      | imm        -> %s  , %s  , %s  , 8'h%8h \
          \n>> has_fs1 | has_fs2 | has_fs3 | has_fd     -> %0b , %0b , %0b , %0b \
          \n>> fs1     | fs2     | fs3     | fd         -> %s  , %s  , %s  , %s \
          \n>>>>\n",
          instr_f.instr_name.name(), 
          instr_f.has_rs1,    instr_f.has_rs2,    instr_f.has_rd,     instr_f.has_imm,
          instr_f.rs1.name(), instr_f.rs2.name(), instr_f.rd.name(),  instr_f.imm,
          instr_f.has_fs1,    instr_f.has_fs2,    instr_f.has_fs3,    instr_f.has_fd,
          instr_f.fs1.name(), instr_f.fs2.name(), instr_f.fs3.name(), instr_f.fd.name()), UVM_DEBUG);
      end

      // actions after directed instr
      act_post_directed_instr(
        .p_instr(instr),
        .p_instr_zfinx(instr_zfinx),
        .p_instr_f(instr_f),
        .idx(i)
      );

    end // for GEN_N_MANIPULATE_INSTR

    restore_reserved_sp_addr();

    super.post_randomize();
  endfunction: post_randomize
  
  virtual function void print_stream_setting();
    `uvm_info(_header, $sformatf(">>%s with base constraints \
      \n>> num_of_instr_per_stream            [%0d] \
      \n>> use_special_operand_patterns       [%0b] \
      \n>> use_fp_only_for_directed_instr     [%0b] \
      \n>> use_no_repetitive_instr_per_stream [%0b] \
      \n>> use_same_instr_per_stream          [%0b] \
      \n>> use_prev_rd_on_next_operands       [%0b] \
      \n>> more_weight_for_fdiv_fsqrt_gen     [%0b] \
      \n>> include_load_store_base_sp         [%0b] \
      ",
      get_name(), num_of_instr_per_stream, use_special_operand_patterns, use_fp_only_for_directed_instr, 
      use_no_repetitive_instr_per_stream, use_same_instr_per_stream, use_prev_rd_on_next_operands, 
      more_weight_for_fdiv_fsqrt_gen, include_load_store_base_sp
      ), UVM_NONE);
  endfunction : print_stream_setting

  // set/restore reserved sp to have fix addr for store instrs
  riscv_reg_t temp_reg; 
  virtual function void set_reserved_sp_addr();
    if (include_load_store_base_sp) begin
      // During exception/irq/debug mode, sp (can be any xreg) is used and must not be alter in this stream.
      // since this steams sometimes uses sp in store instr, we need to set sp to a safer space to prevent
      // from corrupting the main code. Then we restore original sp content at end of stream. 
      // (note: in stream, SP can be any registers not neccessary X2)

        // store original sp content
      riscv_instr instr;
      if (cfg.sp != T0) temp_reg = T0;
      else              temp_reg = T1;
      `SET_GPR_VALUE(temp_reg,32'h8000_0004);
      instr = new riscv_instr::get_rand_instr(.include_instr({SW}));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
        if (has_rs2) {rs2 == SP;}
        if (has_rs1) {rs1 == temp_reg;}
        if (has_imm) {imm == 0;}
      );
      instr_list.push_back(instr);

        // set temporary sp with large value to prevent overlap with maincode
      `SET_GPR_VALUE(SP,32'h8000_0000); // set SP to have higher range
    end
  endfunction: set_reserved_sp_addr
  virtual function void restore_reserved_sp_addr();
    // restore original sp content
    if (include_load_store_base_sp) begin
      riscv_instr instr;
      instr = new riscv_instr::get_rand_instr(.include_instr({LW}));
      `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
        if (has_rd)  {rd == SP;}
        if (has_rs1) {rs1 == temp_reg;}
        if (has_imm) {imm == 0;}
      );
      instr_list.push_back(instr);
    end
  endfunction : restore_reserved_sp_addr

  // clear csr fflags (by through fflags or fcsr)
  // condition: reg rs1 must be keep for csr clr purpose only throughout this stream
  virtual function void clr_crs_fflags(riscv_reg_t rs1);
    riscv_reg_t        i_rs1 = rs1;
    logic [31:0]       csrrw_val = 0;

    csrrw_val[7:5]   = csr_rm;
    csrrw_val[14:13] = csr_mstatus_fs;
    if (!clr_csr_init_done) begin
      if (clr_csr_option) begin `SET_GPR_VALUE(i_rs1,32'h0000_001F); csr_name = CSRRC; end
      else                begin `SET_GPR_VALUE(i_rs1,csrrw_val);     csr_name = CSRRW; end
      clr_csr_init_done = 1;
    end
    if ($urandom_range(1)) directed_csr_access(.instr_name(csr_name), .rs1(i_rs1), .csr(12'h001)); // fflags
    else                   directed_csr_access(.instr_name(csr_name), .rs1(i_rs1), .csr(12'h003)); // fcsr
  endfunction : clr_crs_fflags

  // set dyamic fm
  // condition: this must execute before clr_crs_fflags
  virtual function void set_csr_fm(riscv_reg_t rs1);
    riscv_reg_t        i_rs1 = rs1;
    `SET_GPR_VALUE(i_rs1,csr_rm); csr_name = CSRRW;
    directed_csr_access(.instr_name(csr_name), .rs1(i_rs1), .csr(12'h002)); // frm
  endfunction : set_csr_fm

  // init all the gpr/fpr based on F/zfinx respectly prior directed stream
  // reset fpu fflag prior directed stream
  virtual function void rand_fp_val(output logic [31:0] val);
    int option = $urandom_range(0,4);
    void'(std::randomize(val) with {
      if (option == 0) {val[22:18] == 0; val[17:13] == 0; val[12:8] == 0; val[7:0] != 0;}
      if (option == 1) {val[22:18] == 0; val[17:13] == 0; val[12:8] != 0; val[7:0] == 0;}
      if (option == 2) {val[22:18] == 0; val[17:13] != 0; val[12:8] == 0; val[7:0] == 0;}
      if (option == 3) {val[22:18] != 0; val[17:13] == 0; val[12:8] == 0; val[7:0] == 0;}
      // option == 4 is full rand
    });
  endfunction : rand_fp_val
  virtual function void initialize_regs();
    // set random value on all gpr/fpr registers prior directed stream
    // random fp value with mantissa not zeroes
    if (init_gpr) begin : SET_GPR_RAND_VALUE
      logic [31:0] i_imm;
      for (int i=1; i<32; i++) begin
        riscv_reg_t i_gpr = riscv_reg_t'(i);
        // if (i_gpr inside {cfg.reserved_regs}) continue;
        if (i == int'(cfg.sp)) continue; // do not alter stack pointer
        if (i == int'(cfg.tp)) continue; // do not alter thread pointer
        if (cfg.gen_debug_section) begin
          if (i == int'(cfg_cv32e40p.dp)) continue; // do not alter debug pointer
        end
        rand_fp_val(i_imm);
        `SET_GPR_VALUE(i_gpr,i_imm);
      end
    end
    if (init_fpr) begin : SET_FPR_RAND_VALUE
      logic [31:0] i_imm;
      for (int i=0; i<32; i++) begin
        riscv_fpr_t i_fpr = riscv_fpr_t'(i);
        rand_fp_val(i_imm);
        `SET_FPR_VALUE(i_fpr,i_imm);
      end
    end
    set_reserved_sp_addr();
    set_csr_fm(gp_reg_scratch);
  endfunction : initialize_regs

  virtual function void reset_rand_instr_entry();
    include_instr.delete();     exclude_instr.delete();
    include_category.delete();  exclude_category.delete();
    include_group.delete();     exclude_group.delete();
  endfunction : reset_rand_instr_entry

  // for updating the arguments that use in get_rand_instr 
  virtual function void update_current_instr_arg_list(int idx=0);
    bit select_fp_instr, include_fpc, rand_status;

    rand_status = std::randomize(select_fp_instr) with {select_fp_instr dist {0:=1, 1:=1};};
    assert(rand_status);
    rand_status = std::randomize(include_fpc)     with {include_fpc     dist {0:=3, 1:=1};}; // less weight on fpc
    assert(rand_status);

    if (!use_same_instr_per_stream) include_instr.delete();
    include_group.delete();

    if (is_zfinx) begin
                       include_group = new[1] ({RV32ZFINX});
    end else begin
      if (include_fpc) include_group = new[2] ({RV32F, RV32FC});
      else             include_group = new[1] ({RV32F});
    end

    if (use_fp_only_for_directed_instr) begin
        select_fp_instr = 1;
    end else begin : INSERT_MIXED_INSTR
      exclude_instr = new[33] ({`EXCLUDE_INSTR_LIST});
      if (!select_fp_instr) begin : USE_OTHERS
        include_group.delete();
        if (use_xpulp_as_others_instr)  include_group = new[1] ({RV32X});
        else if ($urandom_range(1))     include_group = new[3] ({RV32I, RV32M, RV32C}); 
        else                            include_group = new[3] ({RV32I, RV32M, RV32X}); 
      end
    end

    if (more_weight_for_fdiv_fsqrt_gen || use_only_for_fdiv_fsqrt_gen) begin
      if (select_fp_instr) // is fp
        if ($urandom_range(1) || use_only_for_fdiv_fsqrt_gen)
          // Metrics DSim throws an "InvalidTypeAssign" error given the (commented out)
          // conditional assigment below. It has been expanded into two assignments.
          // Note that Metrics considers their interpretation of the LRM to be the
          // correct one (that is, the code is illegal). See the link below:
          // https://accellera.mantishub.io/view.php?id=2390
          //     include_instr = new[1] ($urandom_range(1) ? {FDIV_S} : {FSQRT_S});
          if ($urandom_range(1))
            include_instr = new[1] ({FDIV_S});
          else
            include_instr = new[1] ({FSQRT_S});
    end

    if (!include_load_store_base_sp) begin
      if (!(C_SWSP  inside {exclude_instr})) exclude_instr = new[exclude_instr.size()+1] ({exclude_instr, C_SWSP});
      if (!(C_FSWSP inside {exclude_instr})) exclude_instr = new[exclude_instr.size()+1] ({exclude_instr, C_FSWSP});
    end
    else begin : SP_RESERVED_FOR_LOAD_STORE_INSTRS_ONLY
      if (!(C_ADDI4SPN  inside {exclude_instr})) exclude_instr = new[exclude_instr.size()+1] ({exclude_instr, C_ADDI4SPN});
      if (!(C_ADDI16SP  inside {exclude_instr})) exclude_instr = new[exclude_instr.size()+1] ({exclude_instr, C_ADDI16SP});
    end

  endfunction: update_current_instr_arg_list

  // placeholder to insert additonal instr if there is any prior directed instr
  virtual function void add_instr_prior_directed_instr(riscv_instr instr, int idx=0);
    if (is_fp_instr) begin
      if (en_clr_fflags_af_instr)
        clr_crs_fflags(gp_reg_scratch);
    end
  endfunction : add_instr_prior_directed_instr

  virtual function void update_next_instr_arg_list(riscv_instr prev_instr=null, int idx=0);
    if (use_no_repetitive_instr_per_stream && prev_instr != null) begin
      if (!(prev_instr.instr_name inside {exclude_instr})) 
        exclude_instr = new[exclude_instr.size()+1] ({exclude_instr, prev_instr.instr_name});
    end
    if (use_same_instr_per_stream && prev_instr != null) begin
      assert (use_fp_only_for_directed_instr && use_same_instr_per_stream);
      include_instr       = new[1] ({prev_instr.instr_name});
    end
  endfunction: update_next_instr_arg_list

  function void randomize_gpr(riscv_instr instr, int idx=0);
    rand_var_for_inline_constraint();
    instr.set_rand_mode();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      if (local::avail_gp_regs[local::idx].size() > 0) {
        if (has_rs1) {
          rs1 inside {avail_gp_regs[local::idx]};
        }
        if (has_rs2) {
          rs2 inside {avail_gp_regs[local::idx]};
        }
        if (has_rd) {
          rd  inside {avail_gp_regs[local::idx]};
        }
      }
      foreach (reserved_rd[i]) {
        if (has_rs1) {
          rs1 != reserved_rd[i];
        }
        if (has_rs2) {
          rs2 != reserved_rd[i];
          if (local::use_diff_regs_for_operands) {
            rs2 != rs1;
          }
        }
        if (has_rd) {
          rd != reserved_rd[i];
        }
        if (format == CB_FORMAT) {
          rs1 != reserved_rd[i];
        }
      }
      foreach (cfg.reserved_regs[i]) {
        if (has_rd) {
          rd != cfg.reserved_regs[i];
        }
        if (format == CB_FORMAT) {
          rs1 != cfg.reserved_regs[i];
        }
      }
      if (has_imm) {
        soft imm == local::imm;
      }
      rm == local::rm;
      use_rounding_mode_from_instr == local::use_rounding_mode_from_instr;
    )

  endfunction: randomize_gpr

  function void randomize_gpr_compress(cv32e40p_riscv_compressed_instr instr, int idx=0);
    rand_var_for_inline_constraint();
    instr.set_rand_mode();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      if (local::avail_gp_regs[local::idx].size() > 0) {
        if (has_rs1) {
          rs1 inside {avail_gp_regs[local::idx]};
        }
        if (has_rs2) {
          rs2 inside {avail_gp_regs[local::idx]};
        }
        if (has_rd) {
          rd  inside {avail_gp_regs[local::idx]};
        }
      }
      foreach (reserved_rd[i]) {
        if (has_rs1) {
          rs1 != reserved_rd[i];
        }
        if (has_rs2) {
          rs2 != reserved_rd[i];
          if (local::use_diff_regs_for_operands) {
            rs2 != rs1;
          }
        }
        if (has_rd) {
          rd != reserved_rd[i];
        }
        if (format == CB_FORMAT) {
          rs1 != reserved_rd[i];
        }
      }
      foreach (cfg.reserved_regs[i]) {
        if (has_rd) {
          rd != cfg.reserved_regs[i];
        }
        if (format == CB_FORMAT) {
          rs1 != cfg.reserved_regs[i];
        }
      }
      if (local::avail_fp_regs[local::idx].size() >0 ) {
        if (has_fs2) {
          fs2 inside {avail_fp_regs[local::idx]};
        }
        if (has_fd) {
          fd inside {avail_fp_regs[local::idx]};
        }
      }
      if (has_imm) {
        soft imm == local::imm;
      }
      rm == local::rm;
      use_rounding_mode_from_instr == local::use_rounding_mode_from_instr;
    )

  endfunction: randomize_gpr_compress

  function void randomize_gpr_zfinx(riscv_fp_in_x_regs_instr instr, int idx=0);
    rand_var_for_inline_constraint();
    instr.set_rand_mode();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      if (local::avail_gp_regs[local::idx].size() > 0) {
        if (has_rs1) {
          rs1 inside {avail_gp_regs[local::idx]};
        }
        if (has_rs2) {
          rs2 inside {avail_gp_regs[local::idx]};
          if (local::use_diff_regs_for_operands) {
            rs2 != rs1;
          }
        }
        if (has_rs3) {
          rs3 inside {avail_gp_regs[local::idx]};
          if (local::use_diff_regs_for_operands) {
            rs3 != rs2;
            rs3 != rs1;
          }
        }
        if (has_rd) {
          rd  inside {avail_gp_regs[local::idx]};
        }
      }
      foreach (reserved_rd[i]) {
        if (has_rd) {
          rd != reserved_rd[i];
        }
        if (format == CB_FORMAT) {
          rs1 != reserved_rd[i];
        }
      }
      foreach (cfg.reserved_regs[i]) {
        if (has_rd) {
          rd != cfg.reserved_regs[i];
        }
        if (format == CB_FORMAT) {
          rs1 != cfg.reserved_regs[i];
        }
      }
      if (has_imm) {
        soft imm == local::imm;
      }
      rm == local::rm;
      use_rounding_mode_from_instr == local::use_rounding_mode_from_instr;
    )
  endfunction: randomize_gpr_zfinx

  virtual function void randomize_fpr(riscv_floating_point_instr instr, int idx=0);
    rand_var_for_inline_constraint();
    instr.set_rand_mode();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
        if (local::avail_fp_regs[local::idx].size() >0 ) {
          if (has_fs1) {
            fs1 inside {avail_fp_regs[local::idx]};
          }
          if (has_fs2) {
            fs2 inside {avail_fp_regs[local::idx]};
            if (local::use_diff_regs_for_operands) {
              fs2 != fs1;
            }
          }
          if (has_fs3) {
            fs3 inside {avail_fp_regs[local::idx]};
            if (local::use_diff_regs_for_operands) {
              fs3 != fs2;
              fs3 != fs1;
            }
          }
          if (has_fd) {
            fd inside {avail_fp_regs[local::idx]};
          }
        }
        if (local::avail_gp_regs[local::idx].size() > 0) {
          if (has_rs1) {
            rs1 inside {avail_gp_regs[local::idx]};
            !(rs1 inside {reserved_rd, cfg.reserved_regs, ZERO});
          }
          if (has_rs2) {
            rs2 inside {avail_gp_regs[local::idx]};
          }
          if (has_rd) {
            rd  inside {avail_gp_regs[local::idx]};
            !(rd inside {reserved_rd, cfg.reserved_regs, ZERO});
          }
        }
        if (has_imm) {
          soft imm == local::imm;
        }
        rm == local::rm;
        use_rounding_mode_from_instr == local::use_rounding_mode_from_instr;
    )
  endfunction: randomize_fpr

  // for inline constraint usage
  virtual function void rand_var_for_inline_constraint();
    // use different <var> for every instr under same stream
    void'(std::randomize(imm));
    void'(std::randomize(rm));
    void'(std::randomize(use_rounding_mode_from_instr));
  endfunction: rand_var_for_inline_constraint

  // for overriding instruction properties
  virtual function void override_instr(
    riscv_instr                instr=null,
    riscv_floating_point_instr f_instr=null,
    riscv_fpr_t fs1=FT0,  riscv_fpr_t fs2=FT0,  riscv_fpr_t fs3=FT0,  riscv_fpr_t fd=FT0,
    riscv_reg_t rs1=ZERO, riscv_reg_t rs2=ZERO, riscv_reg_t rd=ZERO,  bit[31:0] imm=0);

    // user can expand the list if necessary
    if (instr != null) begin
    unique case(instr.instr_name)
      LUI : begin // LUI rd imm20
              `DV_CHECK_RANDOMIZE_WITH_FATAL(instr, 
                rd == local::rd; imm == local::imm;
              )
            end
    endcase
    end
    // user can expand the list if necessary
    if (f_instr != null) begin
    unique case(f_instr.instr_name)
      FLW:  begin // FLW rd, imm12(rs1)
              `DV_CHECK_RANDOMIZE_WITH_FATAL(f_instr, 
                fd == local::fd; rs1 == local::rs1; imm == local::imm;
              )
            end
      FMV_W_X : begin // fmv.s.x fd, rs1
                  `DV_CHECK_RANDOMIZE_WITH_FATAL(f_instr, 
                    fd == local::fd; rs1 == local::rs1;
                  )
                end
    endcase
    end

  endfunction: override_instr

  // random pattern for specific scenarios
  // note: setting is constraint to meet Imperas coverage
  virtual function void get_xreg_val_for_rand_pattern(ref int unsigned rs_unsigned, ref int rs_signed, ref operand_pattens_t pattern);
    int unsigned rand_case;

    if (pattern == IS_FCVT_RAND_RS1) rand_case = $urandom_range(0,3);
    if (pattern == IS_FMV_RAND_RS1)  rand_case = $urandom_range(0,16);
    if (pattern == IS_FCVT_RAND_RS1 || pattern == IS_FMV_RAND_RS1) begin
      // valid sign   int: from -(2e31) till (2e31)-1
      // valid unsign int: from 0 till (2e32)-1
      unique case (rand_case)
        0: rs_signed = 32'h0;          // 0
        1: rs_signed = 32'h8000_0000;  // -(2e31) or 2e31
        2: rs_signed = 32'h7FFF_FFFF;  // (2e31)-1
        3: rs_signed = 32'hFFFF_FFFF;  // 1 or (2e32)-1
        4: rs_signed = 32'h0080_0000;
        5: rs_signed = 32'h8080_0000;
        6: rs_signed = 32'h0040_0000;
        7: rs_signed = 32'h8040_0000;
        8: rs_signed = 32'h7F7F_FFFF;
        9: rs_signed = 32'hFF7F_FFFF;
       10: rs_signed = 32'h007F_FFFF;
       11: rs_signed = 32'h807F_FFFF;
       12: rs_signed = 32'h1;
       13: rs_signed = 32'h8000_0001;
       14: rs_signed = 32'h7F80_0000;
       15: rs_signed = 32'hFF80_0000;
       16: rs_signed = $urandom_range(32'h7FC0_0000, 32'h7FFF_FFFF);
      endcase
    end
    rs_unsigned = rs_signed;
  endfunction : get_xreg_val_for_rand_pattern

  // for manipulating zfinx instr operands
  virtual function void rand_fp_special_operands_zfinx(riscv_fp_in_x_regs_instr instr=null, int idx=0);

    bit [31:0]        m_operand_a, m_operand_b, m_operand_c;
    operand_pattens_t m_operand_a_pattern, m_operand_b_pattern, m_operand_c_pattern;

    m_operand_a = operand_a[idx]; m_operand_a_pattern = operand_a_pattern[idx];
    m_operand_b = operand_b[idx]; m_operand_b_pattern = operand_b_pattern[idx];
    m_operand_c = operand_c[idx]; m_operand_c_pattern = operand_c_pattern[idx];

    if (!(instr.instr_name inside {FCVT_S_W, FCVT_S_WU})) begin : FOR_SRC_IS_FS
      `MANIPULATE_GPR_OPERANDS(rs1,m_operand_a);
      `MANIPULATE_GPR_OPERANDS(rs2,m_operand_b);
      `MANIPULATE_GPR_OPERANDS(rs3,m_operand_c);
    end
    else if ((instr.instr_name inside {FCVT_S_W, FCVT_S_WU})) begin : FOR_SRC_IS_RS
      if (instr.has_rs1 && operand_a_pattern[idx] != IS_RAND) begin
        int unsigned rs1_unsigned;
        int          rs1_signed;
        m_operand_a_pattern = IS_FCVT_RAND_RS1;
        get_xreg_val_for_rand_pattern(
          .rs_unsigned  (rs1_unsigned),
          .rs_signed    (rs1_signed),
          .pattern      (m_operand_a_pattern)
        );
        m_operand_a = rs1_signed;
        `MANIPULATE_GPR_OPERANDS(rs1, m_operand_a);
      end
    end
    else begin
      `uvm_fatal(_header, $sformatf("[rand_fp_special_operands_zfinx] Invalid")); 
    end
    
  endfunction: rand_fp_special_operands_zfinx
 
  // for manipulating f instr operands
  virtual function void rand_fp_special_operands(riscv_floating_point_instr instr=null, int idx=0);

    bit [31:0]        m_operand_a, m_operand_b, m_operand_c;
    operand_pattens_t m_operand_a_pattern, m_operand_b_pattern, m_operand_c_pattern;
    riscv_reg_t       imm_rd;

    void'(std::randomize(imm_rd)  with {!(imm_rd  inside {cfg.reserved_regs, reserved_rd, instr.rs1, instr.rs2, instr.rd, gp_reg_scratch, gp_reg_sp, ZERO}); }); //  for MANIPULATE_FPR_OPERANDS

    m_operand_a = operand_a[idx]; m_operand_a_pattern = operand_a_pattern[idx];
    m_operand_b = operand_b[idx]; m_operand_b_pattern = operand_b_pattern[idx];
    m_operand_c = operand_c[idx]; m_operand_c_pattern = operand_c_pattern[idx];
    
    if (!(instr.instr_name inside {FCVT_S_W, FCVT_S_WU, FMV_W_X})) begin : FOR_SRC_IS_FS
      `MANIPULATE_FPR_OPERANDS(fs1,m_operand_a);
      `MANIPULATE_FPR_OPERANDS(fs2,m_operand_b);
      `MANIPULATE_FPR_OPERANDS(fs3,m_operand_c);
    end
    else if ((instr.instr_name inside {FCVT_S_W, FCVT_S_WU, FMV_W_X})) begin : FOR_SRC_IS_RS
      if (instr.has_rs1 && operand_a_pattern[idx] != IS_RAND) begin
        int unsigned rs1_unsigned;
        int          rs1_signed;
        if (instr.instr_name == FMV_W_X)  m_operand_a_pattern = IS_FMV_RAND_RS1;
        else                              m_operand_a_pattern = IS_FCVT_RAND_RS1;
        get_xreg_val_for_rand_pattern(
          .rs_unsigned  (rs1_unsigned),
          .rs_signed    (rs1_signed),
          .pattern      (m_operand_a_pattern)
        );
        m_operand_a = rs1_signed;
        `MANIPULATE_GPR_OPERANDS(rs1, m_operand_a);
      end
    end
    else begin
      `uvm_fatal(_header, $sformatf("[rand_fp_special_operands] Invalid")); 
    end
    
  endfunction: rand_fp_special_operands

  // placeholder for post actions after directed instr
  virtual function void act_post_directed_instr(
    riscv_instr                 p_instr=null,
    riscv_fp_in_x_regs_instr    p_instr_zfinx=null, 
    riscv_floating_point_instr  p_instr_f=null, 
    int idx=0);
  endfunction: act_post_directed_instr

  // add b2b nop instr (eq to ADDI x0, x0, 0)
  virtual function void insert_nop_instr(int num=0);
    repeat (num) begin
      riscv_instr nop_instr = new riscv_instr::get_rand_instr(
        .include_instr({NOP})
      );
      instr_list.push_back(nop_instr);
      instr_list[$].comment = {instr_list[$].comment, $sformatf(" [NOP Insertion] ")};
    end
  endfunction: insert_nop_instr

  // add wfi
  virtual function void insert_wfi_instr();
      riscv_instr wfi_instr = new riscv_instr::get_rand_instr(
        .include_instr({WFI})
      );
      instr_list.push_back(wfi_instr);
      instr_list[$].comment = {instr_list[$].comment, $sformatf(" [WFI Insertion] ")};
  endfunction: insert_wfi_instr

  // add illegal
  /* Description:
  *     Directed stream class is to generate a stream of valid riscv_instructions which will be stored in the instr_list.
  *     In order to insert illegal instruction in directed stream, following is the workaround used in this function.
  *     - create a valid riscv_instr (it is just a placeholder to allocate a place for illegal instruction insertion).
  *     - set the helper field "is_illegal_instr" on this valid riscv_instr for post processing of directed stream in cv32e40p_instr_sequence.
  *     - in sequece, once detected valid riscv_instr with is_illegal_instr==1, it will be replaced with illegal instruction generated from riscv_illegal_instr.
  *       (note: riscv_illegal_instr which generate a random illegal instruction based on configuration and return it as string)
  */
  virtual function void insert_illegal_instr();
      riscv_instr illegal_instr;
      illegal_instr = new riscv_instr::get_rand_instr(
        .include_instr({NOP}) // create a placholder insn
      );
      illegal_instr.is_illegal_instr = 1; // tag this as illegal 
      instr_list.push_back(illegal_instr);
      instr_list[$].comment = {instr_list[$].comment, $sformatf(" [Illegal Insertion] ")};
  endfunction: insert_illegal_instr

  // for overriding direct instr operands with previous instruc rd/fd
  virtual function void f_use_prev_rd_on_next_operands(
    riscv_instr                 p_instr=null,
    riscv_fp_in_x_regs_instr    p_instr_zfinx=null, 
    riscv_floating_point_instr  p_instr_f=null, 
    int idx=0);

    int unsigned operand_idx = 0, limit_cnt = 0, limit = 100, rand_idx;

    if (p_instr_zfinx == null && p_instr_f == null && p_instr == null) begin
      // do nothing
    end
    else begin : FUNC_BODY

    curr_has_r_flags = {$bits(curr_has_r_flags){1'b0}};
    curr_has_f_flags = {$bits(curr_has_f_flags){1'b0}};

    if (
        (p_instr_zfinx != null && p_instr_f != null) ||
        (p_instr_zfinx != null && p_instr   != null) ||
        (p_instr_f     != null && p_instr   != null)
    ) begin
      `uvm_fatal(_header, $sformatf("[f_use_prev_rd_on_next_operands] Invalid args combination"));
    end
    else if (p_instr_zfinx != null) begin
      curr_has_r_flags = {p_instr_zfinx.has_rs3, p_instr_zfinx.has_rs2, p_instr_zfinx.has_rs1, p_instr_zfinx.has_rd};
    end
    else if (p_instr_f != null) begin
      curr_has_f_flags = {p_instr_f.has_fs3, p_instr_f.has_fs2, p_instr_f.has_fs1, p_instr_f.has_fd};
      curr_has_r_flags = {1'b0, p_instr_f.has_rs2, p_instr_f.has_rs1, p_instr_f.has_rd};
    end
    else if (p_instr != null) begin
      curr_has_r_flags = {1'b0, p_instr.has_rs2, p_instr.has_rs1, p_instr.has_rd};
    end

    if (prev_has_rd_detected) begin : PREV_HAS_RD
      if (curr_has_r_flags[TOTAL_D_AND_S_REG-1:1] != 0) begin : CURR_HAS_RS
        do begin
          rand_idx = $urandom_range(1, TOTAL_D_AND_S_REG-1);
          if (curr_has_r_flags[rand_idx] && p_instr_zfinx != null) begin
            unique case(rand_idx) 
              1: p_instr_zfinx.rs1 = prev_rd;
              2: p_instr_zfinx.rs2 = prev_rd;
              3: p_instr_zfinx.rs3 = prev_rd;
            endcase
          end
          if (
            (curr_has_r_flags[rand_idx] && p_instr_f != null) ||
            (curr_has_r_flags[rand_idx] && p_instr   != null)
          ) begin
            unique case(rand_idx) 
              1: if (p_instr_f != null) p_instr_f.rs1 = prev_rd; else p_instr.rs1 = prev_rd;
              2: if (p_instr_f != null) p_instr_f.rs2 = prev_rd; else p_instr.rs2 = prev_rd;
            endcase
          end
          limit_cnt++;
          if (limit_cnt == limit) begin
            `uvm_fatal(_header, $sformatf("[f_use_prev_rd_on_next_operands] Reached limit_cnt"));
          end
        end
        while (!curr_has_r_flags[rand_idx]);
      end // CURR_HAS_RS
    end // PREV_HAS_RD

    if (prev_has_fd_detected) begin : PREV_HAS_FD
      if (curr_has_f_flags[TOTAL_D_AND_S_REG-1:1] != 0) begin : CURR_HAS_FS
        do begin
          rand_idx = $urandom_range(1, TOTAL_D_AND_S_REG-1);
          if (curr_has_f_flags[rand_idx]) begin
            unique case(rand_idx) 
              1: p_instr_f.fs1 = prev_fd;
              2: p_instr_f.fs2 = prev_fd;
              3: p_instr_f.fs3 = prev_fd;
            endcase
          end
          limit_cnt++;
          if (limit_cnt == limit) begin
            `uvm_fatal(_header, $sformatf("[f_use_prev_rd_on_next_operands] limit_cnt reached"));
          end
        end
        while (!curr_has_f_flags[rand_idx]);
      end // CURR_HAS_FS
    end // PREV_HAS_FD

    if (curr_has_r_flags[0]) prev_rd = (p_instr_zfinx != null) ? p_instr_zfinx.rd : 
                                       ((p_instr_f    != null) ? p_instr_f.rd : p_instr.rd); 
    if (curr_has_f_flags[0]) prev_fd = p_instr_f.fd;

    prev_has_r_flags = curr_has_r_flags;
    prev_has_f_flags = curr_has_f_flags;
    if (prev_has_r_flags[0]) prev_has_rd_detected = 1;
    if (prev_has_f_flags[0]) prev_has_fd_detected = 1;

    end // FUNC_BODY

  endfunction: f_use_prev_rd_on_next_operands

  // workaround to prevent store instruction to corrupt the code space (OBSOLETED BUT KEEP THE FUNCTION)
  virtual function void wa_prevent_store_on_code_space(riscv_instr instr, int idx=0);

    bit [7:0]                   wa_rand_imm = $urandom_range(1,255);
    riscv_instr                 wa_instr;
    riscv_floating_point_instr  _instr;
    riscv_reg_t                 rd;

    if (is_fp_instr) begin
      `DV_CHECK_FATAL($cast(_instr, instr), "Cast to _instr failed!");
    end
    if (instr.instr_name == C_SWSP || instr.instr_name == C_FSWSP) 
      rd = SP;
    else
      rd = (is_fp_instr) ? _instr.rs1 : instr.rs1;

    wa_instr = new riscv_instr::get_rand_instr(.include_instr({LUI}));
    override_instr(
      .instr  (wa_instr),
      .rd     (rd),
      .imm    ({12'h0, wa_rand_imm, 12'h0}) // yyy_ww_xxx
    ); // +1 overhead instrucion prior store
    instr_list.push_back(wa_instr);
    instr_list[$].comment = {instr_list[$].comment, $sformatf(" [wa_prevent_store_on_code_space] ")};

  endfunction: wa_prevent_store_on_code_space

  // generate instr for csr access (limited use cases)
  virtual function void directed_csr_access(
    riscv_instr_name_t instr_name=INVALID_INSTR, riscv_reg_t rd=ZERO, riscv_reg_t rs1=ZERO,
    logic [11:0] csr=12'h000, int idx=0
  );
    riscv_instr instr;
    assert(instr_name != INVALID_INSTR);
    instr = new riscv_instr::get_rand_instr(
      .include_instr({instr_name})
    );
    instr.set_rand_mode();
    instr.csr_c.constraint_mode(0);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      if (has_rs1) {
        rs1 == local::rs1;
      }
      if (has_rd) {
        rd == local::rd;
      }
      csr == local::csr;
    )
    instr_list.push_back(instr);
  endfunction : directed_csr_access

endclass: cv32e40p_float_zfinx_base_instr_stream


  //
  // extended class that having mixed of others and fp directed_instrs within a stream
  // fp instr generation has more weightage than others isa
  // note: these are default classes that use to cover all the verif plan requirements
  // variant: more_weight_for_fdiv_fsqrt_gen
class cv32e40p_fp_n_mixed_instr_stream extends cv32e40p_float_zfinx_base_instr_stream;

  `uvm_object_utils(cv32e40p_fp_n_mixed_instr_stream)
  `uvm_object_new

  function void pre_randomize();
    super.pre_randomize();
    use_fp_only_for_directed_instr = 0; // directed instr is mixtured of supported isa
  endfunction: pre_randomize

endclass: cv32e40p_fp_n_mixed_instr_stream
class cv32e40p_fp_n_mixed_instr_more_fdiv_fsqrt_stream extends cv32e40p_fp_n_mixed_instr_stream;

  `uvm_object_utils(cv32e40p_fp_n_mixed_instr_more_fdiv_fsqrt_stream)
  `uvm_object_new

  function void pre_randomize();
    super.pre_randomize();
    more_weight_for_fdiv_fsqrt_gen  = 1;
  endfunction: pre_randomize

endclass: cv32e40p_fp_n_mixed_instr_more_fdiv_fsqrt_stream


  //
  // extended class that use to override instr operands with specific patterns
class cv32e40p_fp_w_special_operands_instr_stream extends cv32e40p_float_zfinx_base_instr_stream;

  `uvm_object_utils(cv32e40p_fp_w_special_operands_instr_stream)
  `uvm_object_new

  function void pre_randomize();
    super.pre_randomize();
    use_special_operand_patterns    = 1;
    use_fp_only_for_directed_instr  = 1;
    include_load_store_base_sp      = 0; // exclude store instrs for this stream
  endfunction: pre_randomize

  // to define exclude list for this stream class
  virtual function void update_current_instr_arg_list(int idx=0);
    super.update_current_instr_arg_list(idx);
    // exclude store instrs for this stream
    exclude_instr = new[33+3] ({`EXCLUDE_INSTR_LIST, `FP_STORE_INSTR_LIST});
    // note: it should test all rather just focus on specific instrs as per verifplan. ease for Imperas coverage analysis
    // if (!use_no_repetitive_instr_per_stream && !use_same_instr_per_stream) begin
    //   exclude_instr = new[exclude_instr.size() + 12] (
    //     {exclude_instr, FADD_S, FSUB_S, FMIN_S, FMAX_S, FSGNJ_S, FSGNJN_S, FSGNJX_S, FMV_W_X, FEQ_S, FLT_S, FLE_S, FCLASS_S});
    // end
  endfunction: update_current_instr_arg_list

endclass: cv32e40p_fp_w_special_operands_instr_stream


  //
  // extended class that use to override current directed_instr operands with previous rd/fd (previous does not mean in b2b instr manner)
  // note: this is additional class that use to improve the coverage defined in verif plan
class cv32e40p_fp_w_prev_rd_as_operand_instr_stream extends cv32e40p_float_zfinx_base_instr_stream;

  `uvm_object_utils(cv32e40p_fp_w_prev_rd_as_operand_instr_stream)
  `uvm_object_new

  constraint ovr_c_others {
    num_of_instr_per_stream == 20;
  }

  function void pre_randomize();
    super.pre_randomize();
    use_prev_rd_on_next_operands    = 1;
    use_fp_only_for_directed_instr  = 0;
    en_clr_fflags_af_instr          = 0;
    include_load_store_base_sp      = 0; // exclude store instrs for this stream
  endfunction: pre_randomize

  function void post_randomize();
    super.post_randomize();
    clr_crs_fflags(gp_reg_scratch);
  endfunction : post_randomize

  // to define exclude list for this stream class
  virtual function void update_current_instr_arg_list(int idx=0);
    super.update_current_instr_arg_list(idx);
    // exclude store instrs for this stream
    exclude_instr = new[33+10+3] ({`EXCLUDE_INSTR_LIST, `STORE_INSTR_LIST, `FP_STORE_INSTR_LIST});
  endfunction: update_current_instr_arg_list

endclass: cv32e40p_fp_w_prev_rd_as_operand_instr_stream


  //
  // extended class that preceeded mc instr prior directed fp instr
  // note: this is additional class that use to improve the coverage defined in verif plan
  // use if cv32e40p_fp_n_mixed_instr_stream is not able to achive certain % of coverage
class cv32e40p_constraint_mc_fp_instr_stream extends cv32e40p_float_zfinx_base_instr_stream;

  local riscv_instr_name_t    mc_exclude_instr[];
  local int unsigned          mc_instr_latency;

  `ifdef FPU_ADDMUL_LAT
  local int unsigned          fpu_addmul_lat = `FPU_ADDMUL_LAT;
  `else
  local int unsigned          fpu_addmul_lat = 0;
  `endif
  `ifdef FPU_OTHERS_LAT
  local int unsigned          fpu_others_lat = `FPU_OTHERS_LAT;
  `else
  local int unsigned          fpu_others_lat = 0;
  `endif

  `uvm_object_utils(cv32e40p_constraint_mc_fp_instr_stream)
  `uvm_object_new

  constraint ovr_c_others {
    if (is_zfinx) {num_of_instr_per_stream == TOTAL_INSTR_ZFINX_TYPE;}
    else          {num_of_instr_per_stream == TOTAL_INSTR_F_TYPE+TOTAL_INSTR_FC_TYPE;}
  }

  function void pre_randomize();
    super.pre_randomize();
    // cycle through all possible mc instrs for selected directed fp instr per stream
    use_fp_only_for_directed_instr  = 1;
    en_clr_fflags_af_instr          = 0;
    use_same_instr_per_stream       = 1;
    include_load_store_base_sp      = 1; // store sp is randomly used here
  endfunction: pre_randomize

  virtual function void act_post_directed_instr(
    riscv_instr                 p_instr=null,
    riscv_fp_in_x_regs_instr    p_instr_zfinx=null, 
    riscv_floating_point_instr  p_instr_f=null, 
    int idx=0);
    clr_crs_fflags(gp_reg_scratch);
    insert_nop_instr($urandom_range(1,2)); // put some random NOP before next mc fp iteration
  endfunction: act_post_directed_instr

  virtual function void update_current_instr_arg_list(int idx=0);
    super.update_current_instr_arg_list(idx);
    if (is_zfinx) include_group = new[1] ({RV32ZFINX});
    else          include_group = new[1] ({RV32F});
  endfunction: update_current_instr_arg_list

  // stream implementation to insert mc fp instr
  virtual function void add_instr_prior_directed_instr(riscv_instr instr, int idx=0);

    riscv_instr                 mc_instr;
    riscv_fp_in_x_regs_instr    mc_instr_zfinx;
    riscv_floating_point_instr  mc_instr_f;

    if (instr.group inside {RV32F, RV32FC, RV32ZFINX}) begin : BODY

      // Metrics DSim throws an "InvalidTypeAssign" error given the (commented out)
      // conditional assigment below. It has been expanded into two assignments.
      // Note that Metrics considers their interpretation of the LRM to be the
      // correct one (that is, the code is illegal). See the link below:
      // https://accellera.mantishub.io/view.php?id=2390

      riscv_instr_group_t tmp_include_group[];
      if (is_zfinx)
        tmp_include_group = new[1] ({RV32ZFINX});
      else
        tmp_include_group = new[2] ({RV32F, RV32FC});
      mc_instr = new riscv_instr::get_rand_instr(
        .exclude_instr(mc_exclude_instr),
        //.include_group((is_zfinx) ? {RV32ZFINX} : {RV32F, RV32FC})
        .include_group(tmp_include_group)
      );
      update_next_mc_instr(mc_instr);

      if (is_zfinx) begin
        `DV_CHECK_FATAL($cast(mc_instr_zfinx, mc_instr), "Cast to instr_zfinx failed!");
        randomize_gpr_zfinx(mc_instr_zfinx, idx);
        update_mc_instr_latency(mc_instr_zfinx);
        instr_list.push_back(mc_instr_zfinx);
      end
      else if (mc_instr.group == RV32FC) begin
        randomize_gpr(mc_instr);
        if (mc_instr.instr_name inside {`FP_STORE_INSTR_LIST}) begin
          // wa_prevent_store_on_code_space(mc_instr);
          store_instr_gpr_handling(mc_instr);
        end
        update_mc_instr_latency(mc_instr);
        instr_list.push_back(mc_instr);
      end 
      else begin
        `DV_CHECK_FATAL($cast(mc_instr_f, mc_instr), "Cast to instr_f failed!");
        randomize_fpr(mc_instr_f, idx);
        if (mc_instr_f.instr_name inside {`FP_STORE_INSTR_LIST}) begin: SPECIAL_HANDLING_FOR_STORE
          // wa_prevent_store_on_code_space(mc_instr_f);
          store_instr_gpr_handling(mc_instr_f);
        end
        update_mc_instr_latency(mc_instr_f);
        instr_list.push_back(mc_instr_f);
      end
      instr_list[$].comment = {instr_list[$].comment, $sformatf(" [add_instr_prior_directed_instr] ")};

      rand_fill_mc_latency_w_instrs(
        .instr(mc_instr), .instr_zfinx(mc_instr_zfinx), .instr_f(mc_instr_f)
      );

    end // BODY

  endfunction : add_instr_prior_directed_instr

  // for cycle through all posible mc instr
  virtual function void update_next_mc_instr(riscv_instr prev_instr=null);
    int size = mc_exclude_instr.size();
    if (prev_instr != null && !(prev_instr.instr_name inside {mc_exclude_instr})) begin
      mc_exclude_instr       = new[size+1] (mc_exclude_instr);
      mc_exclude_instr[size] = prev_instr.instr_name;
    end
  endfunction: update_next_mc_instr

  // to update mc instr latency
  virtual function void update_mc_instr_latency(riscv_instr mc_instr=null);

    unique case(mc_instr.instr_name)
      FLW, FSW:                   begin mc_instr_latency = 1; end // table 12.1
      C_FLW, C_FSW:               begin mc_instr_latency = 1; end
      C_FLWSP, C_FSWSP:           begin mc_instr_latency = 1; end
      FMADD_S, FMSUB_S:           begin mc_instr_latency = 1 + fpu_addmul_lat; end // table 12.1
      FNMSUB_S, FNMADD_S:         begin mc_instr_latency = 1 + fpu_addmul_lat; end
      FADD_S, FSUB_S:             begin mc_instr_latency = 1 + fpu_addmul_lat; end
      FMUL_S:                     begin mc_instr_latency = 1 + fpu_addmul_lat; end
      FMIN_S, FMAX_S:             begin mc_instr_latency = 1 + fpu_addmul_lat; end
      FDIV_S, FSQRT_S:            begin mc_instr_latency = $urandom_range(1,19); end // table 12.1
      FSGNJ_S,FSGNJN_S, FSGNJX_S: begin mc_instr_latency = 1 + fpu_others_lat; end // table 12.1
      FCVT_W_S, FCVT_WU_S:        begin mc_instr_latency = 1 + fpu_others_lat; end
      FEQ_S, FLT_S, FLE_S:        begin mc_instr_latency = 1 + fpu_others_lat; end
      FCLASS_S:                   begin mc_instr_latency = 1 + fpu_others_lat; end
      FCVT_S_W,FCVT_S_WU:         begin mc_instr_latency = 1 + fpu_others_lat; end
      FMV_W_X, FMV_X_W:           begin mc_instr_latency = 1 + fpu_others_lat; end
    endcase

  endfunction: update_mc_instr_latency

  // to fill up mc latency period with random instr
  // to delay the directed_instr insertion with deterministic delay
  virtual function void rand_fill_mc_latency_w_instrs(
    riscv_instr                 instr=null,
    riscv_fp_in_x_regs_instr    instr_zfinx=null,
    riscv_floating_point_instr  instr_f=null
  );

    riscv_instr   rand_instr;
    int           rand_instr_latency;
    int           rand_mc_latency = $urandom_range(0,mc_instr_latency);
    int           loop_cnt = 0;

    assert(!(instr == null && instr_zfinx == null && instr_f == null));
    assert(rand_mc_latency >= 0);

    while (!(loop_cnt == 100) && rand_mc_latency > 0) begin
      int p_rand_mc_latency = rand_mc_latency;
      bit skip = 0, is_csr = 0;
      unique case ($urandom_range(0,1))
        0:  begin : INSERT_INTEGER_COMPUTATION_INSTR
              rand_instr = new riscv_instr::get_rand_instr(
                .include_instr(`RV32I_INT_COMP_INSTR_LIST),
                .include_group({RV32I})
              );
              rand_mc_latency = rand_mc_latency - 1; // determistic
            end
        1:  begin : INSERT_MULTIPLICATION_INSTR
              rand_instr = new riscv_instr::get_rand_instr(
                .include_instr(`RV32M_MULH_INSTR_LIST),
                .include_group({RV32M})
              );
              if ((rand_mc_latency - 5) < 0) skip = 1;
              else rand_mc_latency = rand_mc_latency - 5; // determistic
            end
        2:  begin : INSERT_CSR_ACCCESS // exclude this option because csr access get stalled after mult apu insn
              bit           is_4mc    = $urandom_range(1);
              logic [11:0]  addr_csr  = (is_4mc) ? 12'h305 : 12'h340; // mtvec(4) : mscratch(1)
              is_csr = 1;
              rand_instr = new riscv_instr::get_rand_instr(
                .include_instr({CSRRW})
              );
              rand_instr.set_rand_mode();
              rand_instr.csr_c.constraint_mode(0);
              `DV_CHECK_RANDOMIZE_WITH_FATAL(rand_instr,
                if (has_rs1) {
                  rs1 == local::gp_reg_scratch;
                }
                if (has_rd) {
                  rd == ZERO;
                }
                csr == local::addr_csr;
              )
              if ((rand_mc_latency - 1 - is_4mc*3) < 0) skip = 1;
              else rand_mc_latency = rand_mc_latency - 1 - is_4mc*3;
            end
      endcase
      if (!skip) begin
        // fillng_instr need to have no rd/rs dependency on fp instr so that pipeline can go through
        reserved_rd.delete();
        if (instr_zfinx != null) begin
          if (instr_zfinx.has_rs1) begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr_zfinx.rs1}); end
          if (instr_zfinx.has_rs2) begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr_zfinx.rs2}); end
          if (instr_zfinx.has_rs3) begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr_zfinx.rs3}); end
          if (instr_zfinx.has_rd)  begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr_zfinx.rd}); end
        end 
        else if (instr != null) begin
          if (instr.has_rs1) begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr.rs1}); end
          if (instr.has_rs2) begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr.rs2}); end
          if (instr.has_rd)  begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr.rd}); end
        end
        else begin
          if (instr_f.has_rs1) begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr_f.rs1}); end
          if (instr_f.has_rs2) begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr_f.rs2}); end
          if (instr_f.has_rd)  begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr_f.rd}); end
        end
        if (!is_csr) randomize_gpr(rand_instr);
        instr_list.push_back(rand_instr);
        instr_list[$].comment = {instr_list[$].comment, $sformatf(" [rand_fill_mc_latency_w_instrs - %0d cycles] ", p_rand_mc_latency)};
        reserved_rd.delete();
      end
      loop_cnt++;
    end // while

    if (loop_cnt == 100) begin
      `uvm_fatal(_header, $sformatf("rand_mc_latency not able to get filled up. Please revise"));
    end

  endfunction: rand_fill_mc_latency_w_instrs

endclass: cv32e40p_constraint_mc_fp_instr_stream


  //
  // extended class to stress on operands forwarding
  // info: https://en.wikipedia.org/wiki/Operand_forwarding
  // note: Similar to cv32e40p_fp_w_prev_rd_as_operand_instr_stream but is more focus compare to it.
  //       Forwarding paths and write-back logic are shared for the integer and floating point operations 
  //       and are not replicated.
class cv32e40p_fp_op_fwd_instr_stream extends cv32e40p_float_zfinx_base_instr_stream;

  `uvm_object_utils(cv32e40p_fp_op_fwd_instr_stream)
  `uvm_object_new

  int unsigned                num_of_instr_per_block;
  int unsigned                num_of_fp_instr_per_block;
  riscv_instr                 i_instr_list[$];
  instr_type_t                instr_order_per_block[];
  forward_pattern_t           next_instr_pattern;
  riscv_reg_t                 prev_rd, prev_rs1, prev_rs2, prev_rs3;
  bit [TOTAL_D_AND_S_REG-1:0] prev_instr_has_gpr; // rd-rs1-rs2-rs3

  rand bit            fp_first_instr_per_block;
  rand int unsigned   fp_cnt_percent_per_block;
  rand bit            shuffle_instr_per_block;

  constraint ovr_c_others {
    num_of_instr_per_stream == 100;
    num_of_instr_per_stream % num_of_instr_per_block == 0;
    fp_cnt_percent_per_block != 0;
    fp_cnt_percent_per_block % 10 == 0;
    soft fp_first_instr_per_block dist {1 := 4, 0 := 1};
    soft fp_cnt_percent_per_block dist {20 := 2, 30 := 5, 40 :=3, 50:=2};
    soft shuffle_instr_per_block == 0;
  }

  constraint ovr_c_avail_gp_regs {
    foreach (avail_gp_regs[i]) {
      avail_gp_regs[i].size() == XLEN - cfg.reserved_regs.size() - reserved_rd.size() - 3; // 3 are ZERO, gp_reg_scratch, gp_reg_sp
      foreach (avail_gp_regs[i][j]) {
        !(avail_gp_regs[i][j] inside {ZERO, gp_reg_scratch, gp_reg_sp});
      }
    }
  }

  function void pre_randomize();
    super.pre_randomize();
    use_fp_only_for_directed_instr  = 0;
    en_clr_fflags_af_instr          = 0;
    num_of_instr_per_block          = 10;
    include_load_store_base_sp      = 0; // exclude store instrs for this stream
    assert (num_of_instr_per_block  != 0 && num_of_instr_per_block%10 == 0);
  endfunction: pre_randomize

  virtual function void print_stream_setting();
    super.print_stream_setting();
    `uvm_info(_header, $sformatf(">>%s with extended constraints \
      \n>> num_of_instr_per_block             [%0d] \
      \n>> fp_cnt_percent_per_block           [%0d percent] \
      \n>> fp_first_instr_per_block           [%0b] \
      \n>> shuffle_instr_per_block            [%0b] \
      ",
      get_name(), num_of_instr_per_block, fp_cnt_percent_per_block, fp_first_instr_per_block, shuffle_instr_per_block 
      ), UVM_NONE);
  endfunction : print_stream_setting

  // to define exclude list for this stream class
  virtual function void update_current_instr_arg_list(int idx=0);
    // exclude store instrs for this stream
    exclude_instr = new[33+8+3] ({`EXCLUDE_INSTR_LIST, `STORE_INSTR_LIST, `FP_STORE_INSTR_LIST});
    // always exclude RV32C because it only uses 8 common gpr/fpr. We cover more than 8 registers here
    exclude_group = new[2] ({RV32C, RV32FC});

    if (instr_order_per_block[idx] == IS_FP) begin
      // Metrics DSim throws an "InvalidTypeAssign" error given the (commented out)
      // conditional assigment below. It has been expanded into two assignments.
      // Note that Metrics considers their interpretation of the LRM to be the
      // correct one (that is, the code is illegal). See the link below:
      // https://accellera.mantishub.io/view.php?id=2390
      //    include_group = new[1] ((is_zfinx) ? {RV32ZFINX} : {RV32F});
      if (is_zfinx)
        include_group = new[1] ({RV32ZFINX});
      else
        include_group = new[1] ({RV32F});

      // f_type has limited instr that uses gpr
      if (!is_zfinx) include_instr = new[7] ({FCVT_W_S, FCVT_WU_S, FCVT_S_W, FCVT_S_WU, FLW, FMV_X_W, FMV_W_X}); // rd,rd,rs,rs,rs,rd,rs
      else           include_instr.delete();
    end
    else begin
      if (use_xpulp_as_others_instr)  include_group = new[1] ({RV32X});
      else if ($urandom_range(1))     include_group = new[3] ({RV32I, RV32M, RV32C});
      else                            include_group = new[3] ({RV32I, RV32M, RV32X});
      include_instr.delete();
    end
  endfunction: update_current_instr_arg_list

  virtual function void act_post_directed_instr(
    riscv_instr                 p_instr=null,
    riscv_fp_in_x_regs_instr    p_instr_zfinx=null, 
    riscv_floating_point_instr  p_instr_f=null, 
    int idx=0);

    bit [TOTAL_D_AND_S_REG-1:0] instr_has_gpr; // rd-rs1-rs2-rs3
    string instr_name="NA";

    // get current instr has_flags {idx high to low}
    if (!is_fp_instr)                  begin instr_has_gpr = {1'b0,                  p_instr.has_rs2,       p_instr.has_rs1,       p_instr.has_rd};       instr_name = p_instr.instr_name.name(); end
    else if (is_fp_instr && !is_zfinx) begin instr_has_gpr = {1'b0,                  p_instr_f.has_rs2,     p_instr_f.has_rs1,     p_instr_f.has_rd};     instr_name = p_instr_f.instr_name.name(); end
    else if (is_fp_instr && is_zfinx)  begin instr_has_gpr = {p_instr_zfinx.has_rs3, p_instr_zfinx.has_rs2, p_instr_zfinx.has_rs1, p_instr_zfinx.has_rd}; instr_name = p_instr_zfinx.instr_name.name(); end
    else begin
      `uvm_fatal(_header, $sformatf("Unexpected call on act_post_directed_instr() "));
    end
    // execute next_instr_pattern
    if (idx > 0) begin
      int gpr_idx, cnt=0, cnt_limit=40;
      unique case (next_instr_pattern) 
        PREV_RD_IS_CURR_RD :  begin
                                if (!is_fp_instr)             p_instr.rd       = prev_rd;
                                if (is_fp_instr && !is_zfinx) p_instr_f.rd     = prev_rd;
                                if (is_fp_instr && is_zfinx)  p_instr_zfinx.rd = prev_rd;
                              end
        PREV_RD_IS_CURR_RS :  begin
                                do begin
                                  gpr_idx = $urandom_range(1,3); cnt++;
                                  assert (cnt<cnt_limit) else begin `uvm_fatal(_header, $sformatf("cnt limit reached - instr_name is %s with instr_has_gpr %4b", instr_name, instr_has_gpr)); end
                                end
                                while(!instr_has_gpr[gpr_idx]);
                                unique case(gpr_idx)
                                  1: begin
                                    if (!is_fp_instr)             p_instr.rs1       = prev_rd;
                                    if (is_fp_instr && !is_zfinx) p_instr_f.rs1     = prev_rd;
                                    if (is_fp_instr && is_zfinx)  p_instr_zfinx.rs1 = prev_rd;
                                  end
                                  2: begin
                                    if (!is_fp_instr)             p_instr.rs2       = prev_rd;
                                    if (is_fp_instr && !is_zfinx) p_instr_f.rs2     = prev_rd;
                                    if (is_fp_instr && is_zfinx)  p_instr_zfinx.rs2 = prev_rd;
                                  end
                                  3: begin
                                    if (is_fp_instr && is_zfinx)  p_instr_zfinx.rs3 = prev_rd;
                                  end
                                endcase
                              end
        PREV_RS_IS_CURR_RD :  begin
                                do begin
                                  gpr_idx = $urandom_range(1,3); cnt++;
                                  assert (cnt<cnt_limit) else begin `uvm_fatal(_header, $sformatf("cnt limit reached - instr_name is %s with prev_instr_has_gpr %4b", instr_name, prev_instr_has_gpr)); end
                                end
                                while(!prev_instr_has_gpr[gpr_idx]);
                                if (!is_fp_instr)             p_instr.rd       = (gpr_idx==1) ? prev_rs1 : ((gpr_idx==2) ? prev_rs2 : prev_rs3);
                                if (is_fp_instr && !is_zfinx) p_instr_f.rd     = (gpr_idx==1) ? prev_rs1 : ((gpr_idx==2) ? prev_rs2 : prev_rs3);
                                if (is_fp_instr && is_zfinx)  p_instr_zfinx.rd = (gpr_idx==1) ? prev_rs1 : ((gpr_idx==2) ? prev_rs2 : prev_rs3);
                              end
      endcase
    end
    // update next_instr_pattern
    casez (instr_has_gpr)
      4'b??10 : next_instr_pattern = PREV_RS_IS_CURR_RD; // prev: rs
      4'b??11 : next_instr_pattern = forward_pattern_t'($urandom_range(0,2)); // prev: rd, rs1
      4'b0001 : next_instr_pattern = forward_pattern_t'($urandom_range(0,1)); // prev: rd
    endcase
    // update prev_xreg
    if (!is_fp_instr)             begin prev_rd = p_instr.rd;       prev_rs1 = p_instr.rs1;       prev_rs2 = p_instr.rs2;         end
    if (is_fp_instr && !is_zfinx) begin prev_rd = p_instr_f.rd;     prev_rs1 = p_instr_f.rs1;     prev_rs2 = p_instr_f.rs2;       end
    if (is_fp_instr && is_zfinx)  begin prev_rd = p_instr_zfinx.rd; prev_rs1 = p_instr_zfinx.rs1; prev_rs2 = p_instr_zfinx.rs2;   end
    if (is_fp_instr && is_zfinx)  begin prev_rs3 = p_instr_zfinx.rs3; end
    else                          begin prev_rs3 = ZERO; end
    prev_instr_has_gpr = instr_has_gpr;
  endfunction: act_post_directed_instr

  // override because this testcase need special handling
  function void post_randomize();

    print_stream_setting();
    initialize_regs();

    num_of_fp_instr_per_block = (num_of_instr_per_block * fp_cnt_percent_per_block)/100;
    instr_order_per_block = new[(num_of_instr_per_block-num_of_fp_instr_per_block)];
    repeat (num_of_fp_instr_per_block) instr_order_per_block = new[instr_order_per_block.size() + 1] ({instr_order_per_block, IS_FP});

    for (int i = 0; i < num_of_instr_per_stream; i++) begin : GEN_N_MANIPULATE_INSTR

      riscv_instr                 instr;
      riscv_fp_in_x_regs_instr    instr_zfinx;
      riscv_floating_point_instr  instr_f;
      bit has_rd, has_rs1, has_rs2, has_rs3;
      int unsigned loop_cnt, loop_limit = 100;

      if (!(i % num_of_instr_per_block)) begin : RESET_PRIOR_START_OF_BLOCK
        i_instr_list.delete();
        loop_cnt = 0;
        do begin
          if (loop_cnt == loop_limit) begin `uvm_fatal(_header, $sformatf("loop_limit reached [RESET_PRIOR_START_OF_BLOCK]")) end;
          instr_order_per_block.shuffle();
          loop_cnt++;
        end
        while (fp_first_instr_per_block && instr_order_per_block[0] == IS_NON_FP);
        // $display("instr_order_per_block[shuffle] is %p", instr_order_per_block);
      end

      update_current_instr_arg_list(i % num_of_instr_per_block);
      loop_cnt = 0;
      do begin : GEN_INSTR_PER_BLOCK
        if (loop_cnt == loop_limit) begin `uvm_fatal(_header, $sformatf("loop_limit reached [GEN_INSTR_PER_BLOCK]")) end;
        has_rd = 0; has_rs1 = 0; has_rs2 = 0; has_rs3 = 0;
        instr = new riscv_instr::get_rand_instr(
          .include_instr(include_instr),
          .exclude_instr(exclude_instr),
          .include_group(include_group),
          .exclude_group(exclude_group)
        );
        is_fp_instr = (instr.group inside {RV32F, RV32ZFINX});
        if (!is_fp_instr) begin : OTHER_NON_FP_SUPPORTED_EXTENSIONS
          randomize_gpr(instr);
          has_rd  = instr.has_rd; 
          has_rs1 = instr.has_rs1; has_rs2 = instr.has_rs2;
        end
        else if (is_zfinx) begin : EXTENSION_ZFINX
          `DV_CHECK_FATAL($cast(instr_zfinx, instr), "Cast to instr_zfinx failed!");
          randomize_gpr_zfinx(instr_zfinx, i);
          has_rd  = instr_zfinx.has_rd; 
          has_rs1 = instr_zfinx.has_rs1; has_rs2 = instr_zfinx.has_rs2; has_rs3 = instr_zfinx.has_rs3;
        end
        else begin : EXTENSION_F
          `DV_CHECK_FATAL($cast(instr_f, instr), "Cast to instr_f failed!");
          randomize_fpr(instr_f, i);
          has_rd  = instr_f.has_rd; 
          has_rs1 = instr_f.has_rs1; has_rs2 = instr_f.has_rs2;
        end
        loop_cnt++;
      end
      while (
        (i > 0 && next_instr_pattern == PREV_RD_IS_CURR_RD && has_rd  == 0) ||
        (i > 0 && next_instr_pattern == PREV_RD_IS_CURR_RS && has_rs1 == 0) ||
        (i > 0 && next_instr_pattern == PREV_RS_IS_CURR_RD && has_rd  == 0)
      ); // GEN_INSTR_PER_BLOCK

      // actions after directed instr
      act_post_directed_instr(
        .p_instr(instr),
        .p_instr_zfinx(instr_zfinx),
        .p_instr_f(instr_f),
        .idx(i)
      );
      // $display("next_instr_pattern is %s", next_instr_pattern.name());

      if (!is_fp_instr)   i_instr_list.push_back(instr);
      else if (is_zfinx)  i_instr_list.push_back(instr_zfinx);
      else                i_instr_list.push_back(instr_f);

      if (i%num_of_instr_per_block == num_of_instr_per_block-1) begin : POST_PROCESS_BLOCK
        if (shuffle_instr_per_block) 
          i_instr_list.shuffle();
        foreach (i_instr_list[j]) begin
          instr_list.push_back(i_instr_list[j]);
          instr_list[$].comment = {instr_list[$].comment, $sformatf(" Inserted %0s - blk_idx[%0d]", get_name(), j)};
        end
        clr_crs_fflags(gp_reg_scratch);
      end // POST_PROCESS_BLOCK

    end // for GEN_N_MANIPULATE_INSTR

  endfunction: post_randomize

endclass: cv32e40p_fp_op_fwd_instr_stream


  //
  // extended class to stress on operands forwarding mixed with various load store instrs
class cv32e40p_fp_op_fwd_instr_w_loadstore_stream extends cv32e40p_float_zfinx_base_instr_stream;

  load_store_opt_t  load_store_option=NULL;
  bit               use_load_store_w_sp_only;
  bit               use_compress_load_store_only;
  bit               use_post_inc_load_store;
  int unsigned      num_of_load_store_instr;
  bit               post_fp_src_is_load_dest;
  int unsigned      cnt, cnt_limit=100;

  rand int unsigned stream_loops;

  `uvm_object_utils(cv32e40p_fp_op_fwd_instr_w_loadstore_stream)
  `uvm_object_new

  constraint c_stream_loops {
    soft stream_loops inside {[6:10]}; 
    num_of_instr_per_stream == stream_loops;
    solve stream_loops before num_of_instr_per_stream;
  }

  function void pre_randomize();
    super.pre_randomize();
    use_fp_only_for_directed_instr      = 0;
    en_clr_fflags_af_instr              = 0;
    include_load_store_base_sp          = 0; // do not reserved SP
    reserved_rd                         = new[reserved_rd.size()+1] ({reserved_rd, ZERO});
    use_post_inc_load_store             = $urandom_range(1);
  endfunction: pre_randomize

  virtual function void rand_fp_val(output logic [31:0] val);
    if (!use_post_inc_load_store) super.rand_fp_val(val);
    else begin
      void'(std::randomize(val) with {
        val[31:23] == 0; val[22:18] != 0; val[17:13] == 0; val[12:8] == 0; val[7:0] == 0;
      });
    end
  endfunction : rand_fp_val

  virtual function void update_current_instr_arg_list(int idx=0);
  endfunction: update_current_instr_arg_list

  virtual function void manipulate_preceeded_fp(
    riscv_fp_in_x_regs_instr   p_instr_zfinx=null, 
    riscv_floating_point_instr p_instr_f=null
  );
    riscv_reg_t i_rd  = (is_zfinx) ? p_instr_zfinx.rd  : p_instr_f.rd ;
    riscv_reg_t i_rs1 = (is_zfinx) ? p_instr_zfinx.rs1 : p_instr_f.rs1 ;
    riscv_reg_t i_rs2 = (is_zfinx) ? p_instr_zfinx.rs2 : ZERO ;
    riscv_reg_t i_rs3 = (is_zfinx) ? p_instr_zfinx.rs3 : ZERO ;
    logic [31:0] v_rd = $urandom_range(0, 32'hFFFF_FFFF);

    riscv_fpr_t i_fs1 = (is_zfinx) ? FT0 : p_instr_f.fs1;

    assert(!(p_instr_zfinx == null && p_instr_f == null));
    `SET_GPR_VALUE(i_rd, v_rd);

    if (p_instr_zfinx != null) begin
      unique case (p_instr_zfinx.instr_name)
        FADD_S,   FSUB_S    : begin `SET_GPR_VALUE(i_rs1, F_NEG_ZERO_DIV2); `SET_GPR_VALUE(i_rs2, ALL_ZERO); end // rd = rs1 +/- rs2
        FMADD_S,  FMSUB_S   : begin `SET_GPR_VALUE(i_rs1, F_POS_ONE); `SET_GPR_VALUE(i_rs2, F_NEG_ZERO_DIV2); `SET_GPR_VALUE(i_rs3, ALL_ZERO); end // rd = rs1*rs2 +/- rs3
        FNMADD_S, FNMSUB_S  : begin `SET_GPR_VALUE(i_rs1, F_NEG_ONE); `SET_GPR_VALUE(i_rs2, F_NEG_ZERO_DIV2); `SET_GPR_VALUE(i_rs3, ALL_ZERO); end // rd = -rs1*rs2 -/+ rs3
        FMUL_S,   FDIV_S    : begin `SET_GPR_VALUE(i_rs1, F_NEG_ZERO_DIV2); `SET_GPR_VALUE(i_rs2, F_POS_ONE); end // rd = rs1 *// rs2
        FSQRT_S             : begin `SET_GPR_VALUE(i_rs1, F_POS_FOUR); end // rd = sqrt(rs1)
        FMAX_S              : begin `SET_GPR_VALUE(i_rs1, F_POS_FOUR); `SET_GPR_VALUE(i_rs2, ALL_ZERO); end // rd = (rs1 > rs2) ? rs1 : rs2;
        FMIN_S              : begin `SET_GPR_VALUE(i_rs1, F_NEG_ZERO_DIV2); `SET_GPR_VALUE(i_rs2, F_NEG_ZERO_DIV2); end // rd = (rs1 < rs2) ? rs1 : rs2;
        FSGNJ_S, FSGNJX_S   : begin `SET_GPR_VALUE(i_rs1, F_NEG_ZERO_DIV2); `SET_GPR_VALUE(i_rs2, ALL_ZERO); end // rd = sign(rs2),rs1[30:0] / rd = sign(rs1 xor rs2), rs1[30:0]
        FSGNJN_S            : begin `SET_GPR_VALUE(i_rs1, F_NEG_ZERO_DIV2); `SET_GPR_VALUE(i_rs2, F_NEG_ZERO); end // rd = sign(!rs2),rs1[30:0]
        FCVT_S_W, FCVT_S_WU : begin `SET_GPR_VALUE(i_rs1, D_POS_TWO); end // rd(float) = rs1(int)
        FCVT_W_S, FCVT_WU_S : begin `SET_GPR_VALUE(i_rs1, F_POS_VAL1); end // rd(int) = rs1(floating)
      endcase
    end
    else begin
      unique case (p_instr_f.instr_name)
        FCVT_W_S, FCVT_WU_S : begin `SET_FPR_VALUE(i_fs1, F_POS_VAL1); end // rd(int) = fs1
        FMV_X_W             : begin `SET_FPR_VALUE(i_fs1, F_NEG_ZERO_DIV2); end // rd(int) <- fs1
      endcase
    end

  endfunction : manipulate_preceeded_fp

  virtual function void cnt_limit_chk(string str="NULL");
    cnt++;
    if (cnt >= cnt_limit) begin
      `uvm_fatal(_header, $sformatf("[%s] cnt_%0d vs cnt_limit_%0d reached", str, cnt, cnt_limit));
    end
  endfunction : cnt_limit_chk

  // override because this testcase need special handling
  // note:
  // limitation_1 (commented out): on RV32FC due to current workaround at convert2asm in cv32e40p_riscv_compressed_instr
  function void post_randomize();

    print_stream_setting();
    initialize_regs();

    for (int i = 0; i < stream_loops; i++) begin
      riscv_instr                       instr,       instr2,       instr3;
      riscv_fp_in_x_regs_instr          instr_zfinx, instr_zfinx2, instr_zfinx3;
      riscv_floating_point_instr        instr_f,     instr_f2,     instr_f3;
      cv32e40p_riscv_compressed_instr   instr_fc,    instr_fc2;
      riscv_reg_t                       last_load_rd, last_store_rs1, q_load_rd[$];
      riscv_fpr_t                       last_load_fd;
      bit                               has_store, has_load_rd, has_load_fd;

      // rand available options
      use_compress_load_store_only  = $urandom_range(1);
      use_load_store_w_sp_only      = (use_compress_load_store_only) ? $urandom_range(1) : 0;
      load_store_option             = load_store_opt_t'($urandom_range(2));
      num_of_load_store_instr       = $urandom_range(4,8);
      post_fp_src_is_load_dest      = (load_store_option inside {LOAD_ONLY, LOAD_STORE}) ? $urandom_range(1) : 0;

      if (use_compress_load_store_only) begin
        riscv_reg_t rand_avail_gp_regs[];
        riscv_fpr_t rand_avail_fp_regs[];
        void'(std::randomize(rand_avail_gp_regs) with {
          rand_avail_gp_regs.size() == 8;
          unique{rand_avail_gp_regs};
          foreach (rand_avail_gp_regs[j]) {
            rand_avail_gp_regs[j] inside {[S0:A5]};
          }
        });
        void'(std::randomize(rand_avail_fp_regs) with {
          rand_avail_fp_regs.size() == 8;
          // rand_avail_fp_regs.size() == 4; // limitation_1
          unique{rand_avail_fp_regs};
          foreach (rand_avail_fp_regs[j]) {
            rand_avail_fp_regs[j] inside {[FS0:FA5]};
          }
        });
        avail_gp_regs[i] = rand_avail_gp_regs; // override c_avail_gp_regs
        avail_fp_regs[i] = rand_avail_fp_regs; // override c_avail_gp_regs
      end


      // generate preceeded fp - start
      use_diff_regs_for_operands = 1;
      reset_rand_instr_entry();
      exclude_instr    = new[4] ({FEQ_S, FLT_S, FLE_S, FCLASS_S});
      exclude_category = new[2] ({LOAD, STORE});
      if (is_zfinx) include_group = new[1] ({RV32ZFINX});
      else          include_group = new[1] ({RV32F});
      cnt = 0;
      do begin
        cnt_limit_chk("generate_preceeded_fp");
        instr = new riscv_instr::get_rand_instr(
          .exclude_instr(exclude_instr),
          .exclude_category(exclude_category),
          .include_group(include_group)
        );
      end
      while (!instr.has_rd);
      if (is_zfinx) begin
        `DV_CHECK_FATAL($cast(instr_zfinx, instr), $sformatf("Cast to instr_zfinx failed for %s!", instr.instr_name.name()) );
        randomize_gpr_zfinx(instr_zfinx, i);
        if (use_load_store_w_sp_only) instr_zfinx.rd = SP;
        manipulate_preceeded_fp(.p_instr_zfinx(instr_zfinx));
        instr_list.push_back(instr_zfinx);
      end
      else begin
        `DV_CHECK_FATAL($cast(instr_f, instr), $sformatf("Cast to instr_f failed for %s!", instr.instr_name.name()) );
        randomize_fpr(instr_f, i);
        if (use_load_store_w_sp_only) instr_f.rd = SP;
        manipulate_preceeded_fp(.p_instr_f(instr_f));
        instr_list.push_back(instr_f);
      end
      instr_list[$].comment = {instr_list[$].comment, $sformatf("Inserted %s - [generate preceeded fp]", get_name())};
      // generate preceeded fp - end


      // generate load-store instrs - start
      use_diff_regs_for_operands = 1;
      for (int j=0; j<num_of_load_store_instr; j++) begin : INSERT_LOAD_STORE_INSTRS
        reset_rand_instr_entry();
        if      (use_compress_load_store_only && !is_zfinx) include_instr = new[4] ({C_LW, C_SW, C_FLW, C_FSW});
        else if (use_compress_load_store_only && is_zfinx)  include_instr = new[2] ({C_LW, C_SW});
        else                                                exclude_instr = new[8] ({C_LW, C_SW, C_FLW, C_FSW, C_LWSP, C_SWSP, C_FLWSP, C_FSWSP});
        if      (use_load_store_w_sp_only && !is_zfinx)     include_instr = new[4] ({C_LWSP, C_SWSP, C_FLWSP, C_FSWSP});
        else if (use_load_store_w_sp_only && is_zfinx)      include_instr = new[2] ({C_LWSP, C_SWSP});
        if (use_post_inc_load_store) begin : INCLUDE_CV_LOAD_STORE
          unique case (load_store_option)
            STORE_ONLY : include_category = new[2] ({STORE, POST_INC_STORE});
            LOAD_ONLY  : include_category = new[2] ({LOAD, POST_INC_LOAD});
            LOAD_STORE : include_category = new[4] ({LOAD, POST_INC_LOAD, STORE, POST_INC_STORE});
          endcase
        end 
        else begin : EXCLUDE_CV_LOAD_STORE
          unique case (load_store_option)
            STORE_ONLY : include_category = new[1] ({STORE});
            LOAD_ONLY  : include_category = new[1] ({LOAD});
            LOAD_STORE : include_category = new[2] ({LOAD, STORE});
          endcase
        end
        // note: include_category cannot mixed with inclue_group else it will have no effect (group override cat)
        // if (!is_zfinx) include_group = new[4] ({RV32I, RV32C, RV32F, RV32FC});
        // else           include_group = new[3] ({RV32I, RV32C, RV32ZFINX});
        instr2 = new riscv_instr::get_rand_instr(
          .include_instr(include_instr),
          .exclude_instr(exclude_instr),
          .include_category(include_category)
        );
        is_fp_instr   = (instr2.group inside {RV32F, RV32ZFINX});
        // is_fpc_instr  = (instr2.instr_name inside {C_FLW, C_FLWSP}); // limitation_1
        if (!is_fp_instr) begin
          if (is_fpc_instr) begin
            // limitation_1
            // `DV_CHECK_FATAL($cast(instr_fc2, instr2), $sformatf("Cast to instr_fc2 failed for %s!", instr2.instr_name.name()) );
            // randomize_gpr_compress(instr_fc2, i);
            // unique case (instr_fc2.category)
            //   STORE : begin // C_FSW[SP]
            //             instr_fc2.rs1 = (is_zfinx) ? instr_zfinx.rd : instr_f.rd;
            //             last_store_rs1 = instr_fc2.rs1; has_store = 1;
            //           end
            //   LOAD : begin // C_FLW[SP]
            //             if (!is_zfinx) begin
            //               if (instr_fc2.has_rs1 && instr_f.has_rd)      begin instr_fc2.rs1 = instr_f.rd;       last_store_rs1 = instr_fc2.rs1; end
            //             end
            //             else begin
            //               if (instr_fc2.has_rs1 && instr_zfinx.has_rd)  begin instr_fc2.rs1 = instr_zfinx.rd;   last_store_rs1 = instr_fc2.rs1; end
            //             end
            //             if (instr_fc2.has_fd)                           begin last_load_fd = instr_fc2.fd;      has_load_fd = 1; end
            //           end
            // endcase
            // instr_list.push_back(instr_fc2);
          end // is_fpc_instr
          else begin
            randomize_gpr(instr2, i);
            unique case (instr2.category)
              STORE, POST_INC_STORE : begin // S[B|H|WW], C_SW[SP], C_FSW[SP], CV_S[B|H|W]
                        instr2.rs1 = (is_zfinx) ? instr_zfinx.rd : instr_f.rd;
                        if (instr2.category == POST_INC_STORE && j != num_of_load_store_instr-1) begin // no special handle on last load/store
                          assert(instr2.has_rd); // rd here is rs3 in spec
                          instr2.rd = ZERO;      // prevent post incr to update rs1 that target into code space
                        end
                        last_store_rs1 = instr2.rs1; has_store = 1;
                      end
              LOAD, POST_INC_LOAD : begin // L[B|H|W], C_LW[SP], C_FLW[SP], CV_L[B|H|W|BU|HU]
                        if (!is_zfinx) begin
                          if (instr2.has_rs1 && instr_f.has_rd)       begin instr2.rs1 = instr_f.rd;      last_store_rs1 = instr2.rs1; end
                        end
                        else begin
                          if (instr2.has_rs1 && instr_zfinx.has_rd)   begin instr2.rs1 = instr_zfinx.rd;  last_store_rs1 = instr2.rs1; end
                        end
                        if (instr2.has_rd)                            begin last_load_rd = instr2.rd;     has_load_rd = 1; end
                        if (instr2.category == POST_INC_LOAD && j != num_of_load_store_instr-1) begin // no special handle on last load/store
                          assert(instr2.has_rs2);
                          instr2.rs2 = ZERO;     // prevent post incr to update rs1 that target into code space
                        end
                        cnt = 0;
                        while (instr2.rd == instr2.rs1) begin
                          int unsigned idx = $urandom_range(avail_gp_regs[i].size()-1);
                          cnt_limit_chk("generate_load_store_instrs");
                          instr2.rd = avail_gp_regs[i][idx];
                        end
                        q_load_rd.push_back(instr2.rd);
                      end
            endcase
            instr_list.push_back(instr2);
          end // !is_fpc_instr
        end
        else if (!is_zfinx) begin // e.g FSW, FLW
          `DV_CHECK_FATAL($cast(instr_f2, instr2), $sformatf("Cast to instr_f2 failed for %s!", instr2.instr_name.name()) );
          randomize_fpr(instr_f2, i);
          unique case (instr_f2.category)
            STORE : begin
                      instr_f2.rs1   = instr_f.rd; 
                      last_store_rs1 = instr_f2.rs1; 
                    end
            LOAD  : begin
                        if (instr_f2.has_rs1 && instr_f.has_rd)     begin instr_f2.rs1 = instr_f.rd;    last_store_rs1 = instr_f2.rs1; end
                        if (instr_f2.has_fd)                        begin last_load_fd = instr_f2.fd;   has_load_fd = 1; end
                    end
          endcase
          instr_list.push_back(instr_f2);
        end
        else begin
          `uvm_fatal(_header, $sformatf("[generate load-store instrs] Invalid"));
        end
        instr_list[$].comment = {instr_list[$].comment, $sformatf("Inserted %s - [generate load-store]", get_name())};
      end
      // generate load-store instrs - end


      // generate post fp - start
      use_diff_regs_for_operands = 0;
      reset_rand_instr_entry();
      exclude_category = new[2] ({LOAD, STORE});
      if (is_zfinx) include_group = new[1] ({RV32ZFINX});
      else          include_group = new[1] ({RV32F});
      cnt = 0;
      do begin
        cnt_limit_chk("generate_post_fp - rd");
        instr3 = new riscv_instr::get_rand_instr(
          .exclude_category(exclude_category),
          .include_group(include_group)
        );
      end
      while (!instr3.has_rd);
      cnt = 0;
      if (is_zfinx) begin
        `DV_CHECK_FATAL($cast(instr_zfinx3, instr3), $sformatf("Cast to instr_zfinx3 failed for %s!", instr3.instr_name.name()) );
        randomize_gpr_zfinx(instr_zfinx3, i);
        if (use_load_store_w_sp_only) instr_zfinx3.rd = SP;
        else                          instr_zfinx3.rd = last_store_rs1;
        if (post_fp_src_is_load_dest && has_load_rd) begin
          do begin
            cnt_limit_chk("generate_post_fp - rs");
            unique case ($urandom_range(2))
              0 : if (instr_zfinx3.has_rs1) begin instr_zfinx3.rs1 = last_load_rd; break; end
              1 : if (instr_zfinx3.has_rs2) begin instr_zfinx3.rs2 = last_load_rd; break; end
              2 : if (instr_zfinx3.has_rs3) begin instr_zfinx3.rs3 = last_load_rd; break; end
            endcase
          end
          while (1);
        end
        instr_list.push_back(instr_zfinx3);
      end
      else begin
        `DV_CHECK_FATAL($cast(instr_f3, instr3), $sformatf("Cast to instr_f3 failed for %s!", instr3.instr_name.name()) );
        randomize_fpr(instr_f3, i);
        if (use_load_store_w_sp_only) instr_f3.rd = SP;
        else                          instr_f3.rd = last_store_rs1;
        if (post_fp_src_is_load_dest && has_load_fd) begin
          do begin
            cnt_limit_chk("generate_post_fp - fs");
            unique case ($urandom_range(2))
              0 : if (instr_f3.has_fs1) begin instr_f3.fs1 = last_load_fd; break; end
              1 : if (instr_f3.has_fs2) begin instr_f3.fs2 = last_load_fd; break; end
              2 : if (instr_f3.has_fs3) begin instr_f3.fs3 = last_load_fd; break; end
            endcase
          end
          while (1);
        end
        instr_list.push_back(instr_f3);
      end
      instr_list[$].comment = {instr_list[$].comment, $sformatf("Inserted %s - [generate post fp]", get_name())};
      // generate post fp - end


      // post actions
      if (q_load_rd.size() != 0) begin : OVERRIDE_USED_LOAD_RD_TO_STORE_SAFEZONE_ADDR
        q_load_rd.sort();
        foreach (q_load_rd[idx]) begin
          riscv_reg_t temp_q_load_rd;
          if (idx != 0) begin
            if (q_load_rd[idx] == q_load_rd[idx-1]) continue;
          end
          temp_q_load_rd = q_load_rd[idx];
          `SET_GPR_VALUE(temp_q_load_rd, F_NEG_ZERO_DIV2);
        end
        q_load_rd.delete();
      end
      clr_crs_fflags(gp_reg_scratch);
      insert_nop_instr(1);

    end // for stream_loops

  endfunction: post_randomize

endclass: cv32e40p_fp_op_fwd_instr_w_loadstore_stream


  //
  // extended class that cycle through all the fp instructions that change fs state from Initial->Dirty and Clean->Dirty
  // note:
  // 1) transistion only valid for F but not ZFINX extension (During ZFINX, FS always in OFF state)
  // 2) this test is similar to custom fpu_mstatus_test but is generated by corev-dv and have certain constraint randomizations
  // todo: assess and consider the feedback in https://github.com/XavierAubert/core-v-verif/pull/70
class cv32e40p_mstatus_fs_stream extends cv32e40p_float_zfinx_base_instr_stream;

  int unsigned loop_cnt_limit = (is_zfinx) ? 1 : 2;
  int unsigned loop_cnt = 0;
  int unsigned total_instr = (is_zfinx) ? TOTAL_INSTR_ZFINX_TYPE : (TOTAL_INSTR_F_TYPE+TOTAL_INSTR_FC_TYPE);

  `uvm_object_utils(cv32e40p_mstatus_fs_stream)
  `uvm_object_new

  constraint ovr_c_others {
    num_of_instr_per_stream == total_instr * loop_cnt_limit;
  }

  function void pre_randomize();
    super.pre_randomize();
    use_fp_only_for_directed_instr      = 0;
    use_no_repetitive_instr_per_stream  = 1;
    include_load_store_base_sp          = 1;
    clr_csr_option                      = 0; // uses CSRRW
    en_clr_fstate                       = (en_clr_fflags_af_instr & !clr_csr_option);
    csr_mstatus_fs                      = 32'd1; // Initial 
  endfunction: pre_randomize

  virtual function void initialize_regs();
    super.initialize_regs();
    clr_crs_fflags(gp_reg_scratch);
    reset_rand_instr_entry();
  endfunction : initialize_regs

  virtual function void update_current_instr_arg_list(int idx=0);

    if (!is_zfinx) include_group = new[2] ({RV32F, RV32FC});
    else           include_group = new[2] ({RV32ZFINX, RV32FC});

    if (idx == 0) loop_cnt++;
    else if (idx != 0 && idx%total_instr == 0) begin
      loop_cnt++;
      assert (loop_cnt <= loop_cnt_limit);
      exclude_instr.delete();
      csr_mstatus_fs = 32'd2; // Clean 
      clr_csr_init_done = 0;  // Update csrrw_val
    end

  endfunction: update_current_instr_arg_list

  virtual function void add_instr_prior_directed_instr(riscv_instr instr, int idx=0);
    super.add_instr_prior_directed_instr(instr, idx);
    if (en_clr_fstate)
      directed_csr_access(.instr_name(CSRRW), .rs1(gp_reg_scratch), .csr(12'h300)); // condition: this must execute before clr_crs_fflags
  endfunction : add_instr_prior_directed_instr

endclass: cv32e40p_mstatus_fs_stream


// ALL FP STREAM CLASSESS - end
