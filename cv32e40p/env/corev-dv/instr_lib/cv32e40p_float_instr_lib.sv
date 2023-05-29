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

// [Dolphin Design updates]
// This file contains stream classes that use to generate fp instructions

// DEFINES used in this class - start
  // constraint for special pattern operands
  // fixme: update the weight again
  // note: DONOT insert " solve enable_special_operand_patterns before operand_``IDX``_pattern;\" at below code, it will limit the constraints (havent root caused)
  `define C_OPERAND_PATTERN(IDX) \
    constraint c_operand_``IDX``_pattern {\
      soft operand_``IDX``_pattern.size() == num_of_instr_per_stream;\
      foreach (operand_``IDX``_pattern[i]) {\
        if (enable_special_operand_patterns) {\
          soft operand_``IDX``_pattern[i] dist { IS_RAND := 4, IS_Q_NAN  := 2, IS_S_NAN              := 2, \
                                                 IS_POSITIVE_ZERO        := 2, IS_NEGATIVE_ZERO      := 2, \
                                                 IS_POSITIVE_INFINITY    := 2, IS_NEGATIVE_INFINITY  := 2, \
                                                 IS_POSITIVE_SUBNORMAL   := 0, IS_NEGATIVE_SUBNORMAL := 0 };\
        } else {\
          soft operand_``IDX``_pattern[i] == IS_RAND;\
        }\
      }\
    } 
  // fixme: pending subnormal definition
  `define C_OPERAND(IDX) \
    constraint c_operand_``IDX {\
      sign_``IDX``.size()     == num_of_instr_per_stream;\
      exp_``IDX``.size()      == num_of_instr_per_stream;\
      mantissa_``IDX``.size() == num_of_instr_per_stream;\
      operand_``IDX``.size()  == num_of_instr_per_stream;\
      foreach (operand_``IDX``[i]) {\
        if (operand_``IDX``_pattern[i] == IS_POSITIVE_ZERO) {\
          sign_``IDX``[i] == 1'b0; exp_``IDX``[i] == 8'h00; mantissa_``IDX``[i] == 23'h0;\
        }\
        if (operand_``IDX``_pattern[i] == IS_NEGATIVE_ZERO) {\
          sign_``IDX``[i] == 1'b1; exp_``IDX``[i] == 8'h00; mantissa_``IDX``[i] == 23'h0;\
        }\
        if (operand_``IDX``_pattern[i] == IS_POSITIVE_INFINITY) {\
          sign_``IDX``[i] == 1'b0; exp_``IDX``[i] == 8'hFF; mantissa_``IDX``[i] == 23'h0;\
        }\
        if (operand_``IDX``_pattern[i] == IS_NEGATIVE_INFINITY) {\
          sign_``IDX``[i] == 1'b1; exp_``IDX``[i] == 8'hFF; mantissa_``IDX``[i] == 23'h0;\
        }\
        if (operand_``IDX``_pattern[i] == IS_Q_NAN) {\
          sign_``IDX``[i] == 1'b1; exp_``IDX``[i] == 8'hFF; mantissa_``IDX``[i][22] == 1'b1;\
        }\
        if (operand_``IDX``_pattern[i] == IS_S_NAN) {\
          sign_``IDX``[i] == 1'b1; exp_``IDX``[i] == 8'hFF; mantissa_``IDX``[i][22] == 1'b0; mantissa_``IDX``[i][21:12] != 0;\
        }\
        operand_``IDX[i] == {sign_``IDX``[i], exp_``IDX``[i], mantissa_``IDX``[i]};\
        solve operand_``IDX``_pattern[i] before sign_``IDX``[i];\
        solve sign_``IDX``[i] before operand_``IDX[i];\
        solve exp_``IDX``[i] before operand_``IDX[i];\
        solve mantissa_``IDX``[i] before operand_``IDX[i];\
      }\
    }

    // Add overhead instructions to override fp instr operands with specific operand pattern
    // LUI->SW->FLW
    `define MANIPULATE_F_INSTR_OPERANDS(FPR,OPERAND) \
      if (instr.has_``FPR && ``OPERAND``_pattern != IS_RAND) begin\
        riscv_instr                 m_instr;\
        riscv_floating_point_instr  f_instr;\
        m_instr = new riscv_instr::get_rand_instr(.include_instr({LUI}));\
        override_instr(\
          .instr  (m_instr),\
          .rd     (imm_rd),\
          .imm    ({12'h0, ``OPERAND``[31:12]})\
        );\
        instr_list.push_back(m_instr);\
        instr_list[$].comment = {instr_list[$].comment, $sformatf(`" [manipulate_f_instr_``OPERAND``][LUI] `")};\
        m_instr = new riscv_instr::get_rand_instr(.include_instr({SW}));\
        override_instr(\
          .instr  (m_instr),\
          .rs2    (imm_rd),\
          .rs1    (mem_rd),\
          .imm    (32'h0)\
        );\
        instr_list.push_back(m_instr);\
        instr_list[$].comment = {instr_list[$].comment, $sformatf(`" [manipulate_f_instr_``OPERAND``][SW] `")};\
        m_instr = new riscv_instr::get_rand_instr(.include_instr({FLW}));\
        `DV_CHECK_FATAL($cast(f_instr, m_instr), "Cast to instr_f failed!");\
        override_instr(\
          .f_instr  (f_instr),\
          .fd       (instr.``FPR``),\
          .rs1      (mem_rd),\
          .imm      (32'h0)\
        );\
        instr_list.push_back(f_instr);\
        instr_list[$].comment = {instr_list[$].comment, $sformatf(`" [manipulate_f_instr_``OPERAND``][FLW] `")};\
      end

    // Add overhead instructions to override zfinx fp instr operands with specific operand pattern
    // LUI->SW->LW
    `define MANIPULATE_ZFINX_INSTR_OPERANDS(GPR,OPERAND) \
      if (instr.has_``GPR && ``OPERAND``_pattern != IS_RAND) begin\
        riscv_instr                 m_instr;\
        m_instr = new riscv_instr::get_rand_instr(.include_instr({LUI}));\
        override_instr(\
          .instr  (m_instr),\
          .rd     (imm_rd),\
          .imm    ({12'h0, ``OPERAND``[31:12]})\
        );\
        instr_list.push_back(m_instr);\
        instr_list[$].comment = {instr_list[$].comment, $sformatf(`" [manipulate_zfinx_instr_``OPERAND``][LUI] `")};\
        m_instr = new riscv_instr::get_rand_instr(.include_instr({SW}));\
        override_instr(\
          .instr  (m_instr),\
          .rs2    (imm_rd),\
          .rs1    (mem_rd),\
          .imm    (32'h0)\
        );\
        instr_list.push_back(m_instr);\
        instr_list[$].comment = {instr_list[$].comment, $sformatf(`" [manipulate_zfinx_instr_``OPERAND``][SW] `")};\
        m_instr = new riscv_instr::get_rand_instr(.include_instr({LW}));\
        override_instr(\
          .instr  (m_instr),\
          .rd     (instr.``GPR``),\
          .rs1    (mem_rd),\
          .imm    (32'h0)\
        );\
        instr_list.push_back(m_instr);\
        instr_list[$].comment = {instr_list[$].comment, $sformatf(`" [manipulate_zfinx_instr_``OPERAND``][LW] `")};\
      end


// DEFINES - end


// others fixme:
// 1) fcvt.s.w - understand this and update for below

// ALL FP STREAM CLASSESS - start
  // base class for fp instruction stream generation
class cv32e40p_float_zfinx_base_instr_stream extends cv32e40p_base_instr_stream;

  localparam TOTAL_FPR              = 32;
  localparam TOTAL_INSTR_F_TYPE     = 26;
  localparam TOTAL_INSTR_ZFINX_TYPE = 22;
  localparam TOTAL_D_AND_S_REG      = 4;

  // typedef - start
  typedef enum bit [3:0] {
    IS_RAND = 0,
    IS_POSITIVE_ZERO,       /* 'd0  */
    IS_NEGATIVE_ZERO,       /* 'd524288 */
    IS_POSITIVE_INFINITY,   /* 'd522240 */
    IS_NEGATIVE_INFINITY,   /* 'd1046528  */
    IS_POSITIVE_SUBNORMAL,
    IS_NEGATIVE_SUBNORMAL,
    IS_Q_NAN,               /* => 'd1047552  */
    IS_S_NAN                /* => 'd1046528 and < 'dd1047552 */
  } operand_pattens_t;
  // typedef - end
  
  // properties - start
  string                  _header;
  bit                     is_zfinx = riscv_instr_pkg::RV32ZFINX inside {riscv_instr_pkg::supported_isa};;
  riscv_instr_name_t      include_instr[];
  riscv_instr_name_t      exclude_instr[];
  bit                     use_diff_instr_per_stream; // use different directed instr per stream
  bit                     use_same_instr_per_stream; // use the same directed instr per stream
  bit                     use_prev_rd_on_next_operands; // use prev instr dest reg for next directed instr operand
  int unsigned            insert_nop_after_instr; // insert NOP after every directed instr per stream

    // for use_prev_rd_on_next_operands implementation usage - start
  riscv_reg_t                 prev_rd;
  riscv_fpr_t                 prev_fd;
  bit [TOTAL_D_AND_S_REG-1:0] prev_has_r_flags, prev_has_f_flags; // use to store prev instr has_* reg flags
  bit [TOTAL_D_AND_S_REG-1:0] curr_has_r_flags, curr_has_f_flags; // use to store curr instr has_* reg flags
    // for use_prev_rd_on_next_operands implementation usage - end

  rand int unsigned       num_of_instr_per_stream;
  rand riscv_reg_t        avail_gp_regs[][];  // regs for extension zfinx and f
  rand riscv_fpr_t        avail_fp_regs[][];  // regs for extension f only
  rand bit [31:0]         imm;
  rand f_rounding_mode_t  rm;
  rand bit                use_rounding_mode_from_instr;

  rand bit                enable_special_operand_patterns;
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
    if (use_diff_instr_per_stream) {
      if (is_zfinx) {soft num_of_instr_per_stream inside {[TOTAL_INSTR_ZFINX_TYPE/2 : TOTAL_INSTR_ZFINX_TYPE]};}
      else          {soft num_of_instr_per_stream inside {[TOTAL_INSTR_F_TYPE/2 : TOTAL_INSTR_F_TYPE]};}
    } else {
      soft num_of_instr_per_stream == 30; // fixed to 30
    }
    num_of_instr_per_stream > 0;
    solve num_of_instr_per_stream before enable_special_operand_patterns;
  }

  constraint c_avail_gp_regs {
    soft avail_gp_regs.size() == num_of_instr_per_stream;
    foreach (avail_gp_regs[i]) {
      soft avail_gp_regs[i].size() == 10; // more buffer as some dedicated gpr should not been used
      unique{avail_gp_regs[i]};
      foreach (avail_gp_regs[i][j]) {
        !(avail_gp_regs[i][j] inside {cfg.reserved_regs, reserved_rd});
      }
    }
  }

  constraint c_avail_fp_regs {
    soft avail_fp_regs.size() == num_of_instr_per_stream;
    foreach (avail_fp_regs[i]) {
      // avail_fp_regs[i].size() > 3; // minimum 4 - fs[1-3] + fd
      avail_fp_regs[i].size() > TOTAL_FPR/2; // widen the range of selection
      soft avail_fp_regs[i].size() < TOTAL_FPR + 1; // total of available fpr
      unique{avail_fp_regs[i]};
    }
  }

  constraint c_enable_special_operand_patterns {
    soft enable_special_operand_patterns == 0;
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
    use_prev_rd_on_next_operands  = 0;
    use_diff_instr_per_stream     = 0;
  endfunction: pre_randomize

  function void post_randomize();
    riscv_instr                 instr;
    riscv_fp_in_x_regs_instr    instr_zfinx;
    riscv_floating_point_instr  instr_f;
    riscv_instr_group_t         include_group[] = (is_zfinx)    ? {RV32ZFINX} : 
                                                  ((XLEN >= 64) ? {RV32F, RV64F} : {RV32F});

    if (use_diff_instr_per_stream && use_same_instr_per_stream) begin: CHECK_SETTING
      `uvm_fatal(_header, $sformatf("Both use_diff_instr_per_stream and use_same_instr_per_stream set HIGH"));
    end

    `uvm_info(_header, $sformatf(">>%s with following constraints \
      \n>> num_of_instr_per_stream            [%0d] \
      \n>> enable_special_operand_patterns    [%0b] \
      \n>> use_diff_instr_per_stream          [%0b] \
      \n>> use_same_instr_per_stream          [%0b] \
      \n>> use_prev_rd_on_next_operands       [%0b] \
      \n>> insert_nop_after_instr             [%0d]", 
      get_name(), num_of_instr_per_stream, enable_special_operand_patterns, 
      use_diff_instr_per_stream, use_same_instr_per_stream, use_prev_rd_on_next_operands,
      insert_nop_after_instr), UVM_NONE);

    if (enable_special_operand_patterns) begin
      foreach (operand_a[i]) begin
        `uvm_info(_header, $sformatf(">> imm20 for specific operand patterns \
          \n>> instr[%0d] operand_a is %0d [%s]\
          \n>> instr[%0d] operand_b is %0d [%s]\
          \n>> instr[%0d] operand_c is %0d [%s]\
          \n>>", 
          i, operand_a[i][31:12], operand_a_pattern[i],
          i, operand_b[i][31:12], operand_b_pattern[i],
          i, operand_c[i][31:12], operand_c_pattern[i]), UVM_DEBUG);
      end
    end

    for (int i = 0; i < num_of_instr_per_stream; i++) begin : GEN_N_MANIPULATE_INSTR

      // directed instr per stream generation
      update_directed_instr_arg_list();
      instr = new riscv_instr::get_rand_instr(
        .include_instr(include_instr),
        .exclude_instr(exclude_instr),
        .include_group(include_group)
      );
      update_next_instr(instr);
      rand_var_for_inline_constraint();

      // [optional] multicycle instr prior directed instr
      insert_mc_instr(include_group, i); 

      // differentiate based on extension
      if (is_zfinx) begin : EXTENSION_ZFINX
        `DV_CHECK_FATAL($cast(instr_zfinx, instr), "Cast to instr_zfinx failed!");
        randomize_gpr_zfinx(instr_zfinx, i);
        if (use_prev_rd_on_next_operands) begin : OVERRIDE_OPERAND_TO_PREV_RD
          f_use_prev_rd_on_next_operands(.p_instr_zfinx(instr_zfinx), .idx(i));
        end
        if (enable_special_operand_patterns) begin : OVERRIDE_OPERANDS_W_SPECIAL_PATTERNS
          manipulate_zfinx_instr_operands(instr_zfinx, i);
        end
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
        `DV_CHECK_FATAL($cast(instr_f, instr), "Cast to instr_f failed!");
        randomize_fpr(instr_f, i);
        if (use_prev_rd_on_next_operands) begin : OVERRIDE_OPERAND_TO_PREV_RD
          f_use_prev_rd_on_next_operands(.p_instr_f(instr_f), .idx(i));
        end
        if (instr_f.instr_name == FSW) begin: SPECIAL_HANDLING_FOR_FLW
          wa_prevent_store_on_code_space(instr_f);
        end
        if (enable_special_operand_patterns) begin : OVERRIDE_OPERANDS_W_SPECIAL_PATTERNS
          manipulate_f_instr_operands(instr_f, i);
        end
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

      if (insert_nop_after_instr) begin
        f_insert_nop_after_instr(insert_nop_after_instr);
      end

    end // for GEN_N_MANIPULATE_INSTR

    super.post_randomize();
  endfunction: post_randomize

  // placeholder for ext class to update the arguments that use in get_rand_instr 
  virtual function void update_directed_instr_arg_list();
  endfunction: update_directed_instr_arg_list

  // placeholder for ext class to insert multicycle instrs
  virtual function void insert_mc_instr(riscv_instr_group_t mc_include_group[$] = {}, int idx=0);
  endfunction : insert_mc_instr

  virtual function void update_next_instr(riscv_instr prev_instr=null);
    if (use_diff_instr_per_stream && prev_instr != null) begin
      int size = exclude_instr.size();
      exclude_instr       = new[size+1] (exclude_instr);
      exclude_instr[size] = prev_instr.instr_name;
    end
    if (use_same_instr_per_stream && prev_instr != null) begin
      include_instr       = new[1];
      include_instr[0]    = prev_instr.instr_name;
    end
  endfunction: update_next_instr

  // for randomizing gpr to be used in this instr
  function void randomize_gpr_zfinx(riscv_fp_in_x_regs_instr instr, int idx=0);
    instr.set_rand_mode();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      if (local::avail_gp_regs[local::idx].size() > 0) {
        if (has_rs1) {
          rs1 inside {avail_gp_regs[local::idx]};
        }
        if (has_rs2) {
          rs2 inside {avail_gp_regs[local::idx]};
        }
        if (has_rs3) {
          rs3 inside {avail_gp_regs[local::idx]};
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
      rm == local::rm;
      use_rounding_mode_from_instr == local::use_rounding_mode_from_instr;
    )
  endfunction: randomize_gpr_zfinx

  // for randomizing fpr to be used in this instr
  virtual function void randomize_fpr(riscv_floating_point_instr instr, int idx=0);
    instr.set_rand_mode();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
        if (local::avail_fp_regs[local::idx].size() >0 ) {
          if (has_fs1) {
            fs1 inside {avail_fp_regs[local::idx]};
          }
          if (has_fs2) {
            fs2 inside {avail_fp_regs[local::idx]};
          }
          if (has_fs3) {
            fs3 inside {avail_fp_regs[local::idx]};
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
        if (instr_name inside {FLW, FSW}) {
          imm == local::imm;
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

    // user to expend the list when necessary
    if (instr != null) begin
    unique case(instr.instr_name)
      LUI : begin // LUI rd imm20
              `DV_CHECK_RANDOMIZE_WITH_FATAL(instr, 
                rd == local::rd; imm == local::imm;
              )
            end
      SW :  begin // SW rs2 imm12(rs1)
              `DV_CHECK_RANDOMIZE_WITH_FATAL(instr, 
                rs2 == local::rs2; rs1 == local::rs1; imm == local::imm;
              )
            end
      LW :  begin // LW rd imm12(rs1)
              `DV_CHECK_RANDOMIZE_WITH_FATAL(instr, 
                rd == local::rd; rs1 == local::rs1; imm == local::imm;
              )
            end
    endcase
    end
    // user to expend the list when needed
    if (f_instr != null) begin
    unique case(f_instr.instr_name)
      FLW:  begin // FLW rd, imm12(rs1)
              `DV_CHECK_RANDOMIZE_WITH_FATAL(f_instr, 
                fd == local::fd; rs1 == local::rs1; imm == local::imm;
              )
            end
    endcase
    end

  endfunction: override_instr

  // for manipulating zfinx instr operands
  virtual function void manipulate_zfinx_instr_operands(riscv_fp_in_x_regs_instr instr, int idx=0);

    bit [31:0]        m_operand_a, m_operand_b, m_operand_c;
    operand_pattens_t m_operand_a_pattern, m_operand_b_pattern, m_operand_c_pattern;
    riscv_reg_t       mem_rd, imm_rd;

    void'(std::randomize(mem_rd) with {!(mem_rd inside {cfg.reserved_regs, reserved_rd, instr.rs1, instr.rs2, instr.rs3, instr.rd});          });
    void'(std::randomize(imm_rd) with {!(imm_rd inside {cfg.reserved_regs, reserved_rd, instr.rs1, instr.rs2, instr.rs3, instr.rd, mem_rd});  });

    if (
      instr.has_rs1 && operand_a_pattern[idx] != IS_RAND ||
      instr.has_rs2 && operand_b_pattern[idx] != IS_RAND ||
      instr.has_rs3 && operand_c_pattern[idx] != IS_RAND
    ) begin : DEFINE_MEM_ADDR
      riscv_instr m_instr;
      m_instr = new riscv_instr::get_rand_instr(.include_instr({LUI}));
      override_instr(
        .instr  (m_instr),
        .rd     (mem_rd),
        .imm    ({12'h0, 8'b1100_0000, 12'h0}) // use higher memory as mailbox
      );
      instr_list.push_back(m_instr);
      instr_list[$].comment = {instr_list[$].comment, $sformatf(" [manipulate_zfinx_instr_operands][mem_addr] ")};
    end // DEFINE_MEM_ADDR

    m_operand_a = operand_a[idx]; m_operand_a_pattern = operand_a_pattern[idx];
    m_operand_b = operand_b[idx]; m_operand_b_pattern = operand_b_pattern[idx];
    m_operand_c = operand_c[idx]; m_operand_c_pattern = operand_c_pattern[idx];
    `MANIPULATE_ZFINX_INSTR_OPERANDS(rs1,m_operand_a)
    `MANIPULATE_ZFINX_INSTR_OPERANDS(rs2,m_operand_b)
    `MANIPULATE_ZFINX_INSTR_OPERANDS(rs3,m_operand_c)
    
  endfunction: manipulate_zfinx_instr_operands
 
  // for manipulating f instr operands
  virtual function void manipulate_f_instr_operands(riscv_floating_point_instr instr, int idx=0);

    bit [31:0]        m_operand_a, m_operand_b, m_operand_c;
    operand_pattens_t m_operand_a_pattern, m_operand_b_pattern, m_operand_c_pattern;
    riscv_reg_t       mem_rd = A2;
    riscv_reg_t       imm_rd = A3;
    
    if (idx == 0 && (
      instr.has_fs1 && operand_a_pattern[idx] != IS_RAND ||
      instr.has_fs2 && operand_b_pattern[idx] != IS_RAND ||
      instr.has_fs3 && operand_c_pattern[idx] != IS_RAND
    )) begin : DEFINE_MEM_ADDR
      riscv_instr m_instr;
      m_instr = new riscv_instr::get_rand_instr(.include_instr({LUI}));
      override_instr(
        .instr  (m_instr),
        .rd     (mem_rd),
        .imm    ({12'h0, 8'b1100_0000, 12'h0}) // use higher memory as mailbox
      );
      instr_list.push_back(m_instr);
      instr_list[$].comment = {instr_list[$].comment, $sformatf(" [manipulate_f_instr_operands][mem_addr] ")};
    end // DEFINE_MEM_ADDR

    m_operand_a = operand_a[idx]; m_operand_a_pattern = operand_a_pattern[idx];
    m_operand_b = operand_b[idx]; m_operand_b_pattern = operand_b_pattern[idx];
    m_operand_c = operand_c[idx]; m_operand_c_pattern = operand_c_pattern[idx];
    `MANIPULATE_F_INSTR_OPERANDS(fs1,m_operand_a)
    `MANIPULATE_F_INSTR_OPERANDS(fs2,m_operand_b)
    `MANIPULATE_F_INSTR_OPERANDS(fs3,m_operand_c)
    
  endfunction: manipulate_f_instr_operands

  // to insert nop after every direct instr
  virtual function void f_insert_nop_after_instr(int num=0);
    repeat (num) begin
      riscv_instr nop_instr = new riscv_instr::get_rand_instr(
        .include_instr({NOP})
      );
      instr_list.push_back(nop_instr);
      instr_list[$].comment = {instr_list[$].comment, $sformatf(" [NOP_after_directed_instr] ")};
    end
  endfunction: f_insert_nop_after_instr

  // for overriding direct instr operands with previous instruc rd/fd
  virtual function void f_use_prev_rd_on_next_operands(
    riscv_fp_in_x_regs_instr    p_instr_zfinx=null, 
    riscv_floating_point_instr  p_instr_f=null, 
    int idx=0);

    int unsigned operand_idx = 0, limit_cnt = 0, limit = 100, rand_idx;

    curr_has_r_flags = {$bits(curr_has_r_flags){1'b0}};
    curr_has_f_flags = {$bits(curr_has_f_flags){1'b0}};

    if ((p_instr_zfinx == null && p_instr_f == null) || 
        (p_instr_zfinx != null && p_instr_f != null)) begin
      `uvm_fatal(_header, $sformatf("[f_use_prev_rd_on_next_operands] Invalid args"));
    end
    else if (p_instr_zfinx != null) begin
      curr_has_r_flags = {p_instr_zfinx.has_rs3, p_instr_zfinx.has_rs2, p_instr_zfinx.has_rs1, p_instr_zfinx.has_rd};
    end
    else if (p_instr_f != null) begin
      curr_has_f_flags = {p_instr_f.has_fs3, p_instr_f.has_fs2, p_instr_f.has_fs1, p_instr_f.has_fd};
      curr_has_r_flags = {0,                 p_instr_f.has_rs2, p_instr_f.has_rs1, p_instr_f.has_rd};
    end

    if (prev_has_r_flags[0]) begin : PREV_HAS_RD
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
          if (curr_has_r_flags[rand_idx] && p_instr_f != null) begin
            unique case(rand_idx) 
              1: p_instr_f.rs1 = prev_rd;
              2: p_instr_f.rs2 = prev_rd;
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

    else if (prev_has_f_flags[0]) begin : PREV_HAS_FD
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

    prev_has_r_flags = curr_has_r_flags;
    prev_has_f_flags = curr_has_f_flags;
    if (curr_has_r_flags[0]) prev_rd = (p_instr_zfinx != null) ? p_instr_zfinx.rd : p_instr_f.rd;
    if (curr_has_f_flags[0]) prev_fd = p_instr_f.fd;

  endfunction: f_use_prev_rd_on_next_operands

  // workaround to prevent FSW from overriding onto the code space
  virtual function void wa_prevent_store_on_code_space(riscv_floating_point_instr instr, int idx=0);

    bit [7:0] wa_rand_imm = $urandom_range(1,255);
    riscv_instr wa_instr;
    wa_instr = new riscv_instr::get_rand_instr(.include_instr({LUI}));
    override_instr(
      .instr  (wa_instr),
      .rd     (instr.rs1),
      .imm    ({12'h0, wa_rand_imm, 12'h0}) // yyy_ww_xxx
    );
    instr_list.push_back(wa_instr);
    instr_list[$].comment = {instr_list[$].comment, $sformatf(" [wa_prevent_store_on_code_space] ")};

  endfunction: wa_prevent_store_on_code_space

endclass: cv32e40p_float_zfinx_base_instr_stream


  //
  // extended class that use to override instr operands with specific patterns
class cv32e40p_fp_w_special_operands_instr_stream extends cv32e40p_float_zfinx_base_instr_stream;

  `uvm_object_utils(cv32e40p_fp_w_special_operands_instr_stream)
  `uvm_object_new

  constraint ovr_c_others {
    num_of_instr_per_stream == 10; // fixed to 10
  }

  constraint ovr_c_enable_special_operand_patterns {
    enable_special_operand_patterns == 1;
  }

  function void pre_randomize();
    super.pre_randomize();
  endfunction: pre_randomize

  // to define exclude list for this stream class
  virtual function void update_directed_instr_arg_list();
    // exclude FLW, FSW and FMV_W_X: no fp regs as operand and by refering to verif plan
    // exclude others: no fp regs as operand and by refering to verif plan
    // fixme: review - should we test all rather just focus sepcific. although others are covered in onespin?
    if (!use_diff_instr_per_stream && !use_same_instr_per_stream) begin
      exclude_instr = new[14];
      exclude_instr = {FLW, FSW, FADD_S, FSUB_S, FMIN_S, FMAX_S, FSGNJ_S, FSGNJN_S, FSGNJX_S, FMV_W_X, FEQ_S, FLT_S, FLE_S, FCLASS_S};
    end
  endfunction: update_directed_instr_arg_list

endclass: cv32e40p_fp_w_special_operands_instr_stream

  //
  // extended class that use to override instr operands with specific patterns
class cv32e40p_fp_w_prev_rd_as_operand_instr_stream extends cv32e40p_float_zfinx_base_instr_stream;

  `uvm_object_utils(cv32e40p_fp_w_prev_rd_as_operand_instr_stream)
  `uvm_object_new

  function void pre_randomize();
    super.pre_randomize();
    use_prev_rd_on_next_operands  = 1;
  endfunction: pre_randomize

  // to define exclude list for this stream class
  virtual function void update_directed_instr_arg_list();
    // exclude FSW: no rd
    exclude_instr = new[1];
    exclude_instr = {FSW};
  endfunction: update_directed_instr_arg_list

endclass: cv32e40p_fp_w_prev_rd_as_operand_instr_stream


  // 
  // extended class that use to override instr operands with specific patterns
class cv32e40p_multicycle_fp_instr_stream extends cv32e40p_float_zfinx_base_instr_stream;

  local bit                   use_diff_mc_fp_instr = 1;
  local riscv_instr_group_t   mc_include_group[];
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

  `uvm_object_utils(cv32e40p_multicycle_fp_instr_stream)
  `uvm_object_new

  function void pre_randomize();
    super.pre_randomize();
    // cycle through all possible mc instrs for one directed fp instr
    use_same_instr_per_stream = 1;
    insert_nop_after_instr    = 2;
  endfunction: pre_randomize

  constraint ovr_c_others {
    if (is_zfinx) {num_of_instr_per_stream == TOTAL_INSTR_ZFINX_TYPE;}
    else          {num_of_instr_per_stream == TOTAL_INSTR_F_TYPE;}
  }

  // stream implementation to insert mc fp instr
  virtual function void insert_mc_instr(riscv_instr_group_t mc_include_group[$] = {}, int idx=0);

    riscv_instr                 mc_instr;
    riscv_fp_in_x_regs_instr    mc_instr_zfinx;
    riscv_floating_point_instr  mc_instr_f;

    if (mc_include_group.size() == 0) begin
      `uvm_fatal(_header, $sformatf("mc_include_group need to be defined"));
    end

    mc_instr = new riscv_instr::get_rand_instr(
      .exclude_instr(mc_exclude_instr),
      .include_group(mc_include_group)
    );
    update_next_mc_instr(mc_instr);

    if (is_zfinx) begin
      `DV_CHECK_FATAL($cast(mc_instr_zfinx, mc_instr), "Cast to instr_zfinx failed!");
      randomize_gpr_zfinx(mc_instr_zfinx, idx);
      update_mc_instr_latency(mc_instr_zfinx);
      instr_list.push_back(mc_instr_zfinx);
    end
    else begin
      `DV_CHECK_FATAL($cast(mc_instr_f, mc_instr), "Cast to instr_f failed!");
      randomize_fpr(mc_instr_f, idx);
      if (mc_instr_f.instr_name == FSW) begin: SPECIAL_HANDLING_FOR_FLW
        wa_prevent_store_on_code_space(mc_instr_f);
      end
      update_mc_instr_latency(mc_instr_f);
      instr_list.push_back(mc_instr_f);
    end
    instr_list[$].comment = {instr_list[$].comment, $sformatf(" [insert_mc_instr] ")};

    rand_fill_mc_latency_w_instrs();

  endfunction : insert_mc_instr

  // for cycle through all posible mc instr
  virtual function void update_next_mc_instr(riscv_instr prev_instr=null);
    if (prev_instr != null) begin
      int size = mc_exclude_instr.size();
      mc_exclude_instr       = new[size+1] (mc_exclude_instr);
      mc_exclude_instr[size] = prev_instr.instr_name;
    end
  endfunction: update_next_mc_instr

  // to update mc instr latency
  virtual function void update_mc_instr_latency(riscv_instr mc_instr=null);

    // fixme: review this
    unique case(mc_instr.instr_name)
      FLW, FSW:                   begin mc_instr_latency = 2; end
      FMV_W_X, FMV_X_W:           begin mc_instr_latency = 2; end
      FMADD_S, FMSUB_S:           begin mc_instr_latency = 1 + fpu_addmul_lat; end
      FNMSUB_S, FNMADD_S:         begin mc_instr_latency = 1 + fpu_addmul_lat; end
      FADD_S, FSUB_S:             begin mc_instr_latency = 1 + fpu_addmul_lat; end
      FMUL_S:                     begin mc_instr_latency = 1 + fpu_addmul_lat; end
      FMIN_S, FMAX_S:             begin mc_instr_latency = 1 + fpu_addmul_lat; end
      // FDIV_S, FSQRT_S:            begin mc_instr_latency = $urandom_range(4,9); end // actual is 1...12
      FDIV_S, FSQRT_S:            begin mc_instr_latency = $urandom_range(1,12); end // todo: review needed
      FSGNJ_S,FSGNJN_S, FSGNJX_S: begin mc_instr_latency = 1 + fpu_others_lat; end
      FCVT_W_S, FCVT_WU_S:        begin mc_instr_latency = 1 + fpu_others_lat; end
      FEQ_S, FLT_S, FLE_S:        begin mc_instr_latency = 1 + fpu_others_lat; end
      FCLASS_S:                   begin mc_instr_latency = 1 + fpu_others_lat; end
      FCVT_S_W,FCVT_S_WU:         begin mc_instr_latency = 1 + fpu_others_lat; end
    endcase

  endfunction: update_mc_instr_latency

  // to fill up mc latency period with random instr
  virtual function void rand_fill_mc_latency_w_instrs();

    riscv_instr   rand_instr;
    int           rand_instr_latency;
    int           rand_mc_latency = $urandom_range(0,mc_instr_latency);
    int           loop_cnt = 0;

    assert(rand_mc_latency >= 0);

    // fixme: add case for xpulp as rand_insrt 
    while (!(loop_cnt == 100) && rand_mc_latency > 0) begin
      bit skip = 0;
      case ($urandom_range(0,1))
        0:  begin : INSERT_INTEGER_COMPUTATION_INSTR
              rand_instr = new riscv_instr::get_rand_instr(
                .include_instr({ADD, ADDI, SUB, LUI, AUIPC,
                                SLL, SLLI, SRL, SRLI, SRA, SRAI,
                                XOR, XORI, OR, ORI, AND, ANDI}),
                .include_group({RV32I})
              );
              rand_mc_latency = rand_mc_latency - 1;
            end
        1:  begin : INSERT_MULTIPLICATION_INSTR
              rand_instr = new riscv_instr::get_rand_instr(
                .include_instr({MULH, MULHSU, MULHU}),
                .include_group({RV32M})
              );
              if ((rand_mc_latency - 5) < 0) 
                skip = 1;
              else
                rand_mc_latency = rand_mc_latency - 5;
            end
      endcase
      if (!skip) begin
        randomize_gpr(rand_instr);
        instr_list.push_back(rand_instr);
        instr_list[$].comment = {instr_list[$].comment, $sformatf(" [rand_fill_mc_latency_w_instrs] ")};
      end
      loop_cnt++;
    end

    if (loop_cnt == 100) begin
      `uvm_fatal(_header, $sformatf("rand_mc_latency not able to get filled up. Please revise"));
    end

  endfunction: rand_fill_mc_latency_w_instrs

endclass: cv32e40p_multicycle_fp_instr_stream

// ALL FP STREAM CLASSESS - end
