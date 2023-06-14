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

// fixme:
// 1) we need to have a method to have more weight on fdiv and fsqrt when generating directed fp instr
// 2) remove all stuff related to temp_exclude_fdiv_fsqrt once issues are fixed

// ALL FP (SINGLE PERCISION) STREAM CLASSESS - start
  // base class for fp instruction stream generation
  // all the directed instrs generated in a stream are fp instr 

class cv32e40p_float_zfinx_base_instr_stream extends cv32e40p_base_instr_stream;

  localparam TOTAL_INSTR_F_TYPE     = 26;
  localparam TOTAL_INSTR_ZFINX_TYPE = 22;
  localparam TOTAL_D_AND_S_REG      = 4; // total available dest+src = total_[r/f]s + total[r/f]d = 3 + 1

  // typedef - start
  typedef enum bit [4:0] {
    IS_RAND = 0,
    IS_POSITIVE_ZERO,       /* 'd0  */
    IS_NEGATIVE_ZERO,       /* 'd524288 */
    IS_POSITIVE_INFINITY,   /* 'd522240 */
    IS_NEGATIVE_INFINITY,   /* 'd1046528  */
    IS_POSITIVE_MAX,
    IS_NEGATIVE_MAX,
    IS_POSITIVE_MIN,
    IS_NEGATIVE_MIN,
    IS_POSITIVE_SUBNORMAL,
    IS_NEGATIVE_SUBNORMAL,
    IS_Q_NAN,               /* => 'd1047552 < mantissa all_ones  */
    IS_S_NAN,               /* => 'd1046528 and < 'dd1047552 */
    W_IS_AT_PERCISION_MAX,
    W_IS_AT_PERCISION_MIN,
    W_IS_WITHIN_PERCISION_LIMIT,
    W_IS_MAX_INTEGER,
    W_IS_MIN_INTEGER
  } operand_pattens_t;
  // typedef - end
  
  `include "instr_lib/cv32e40p_float_instr_lib_defines.sv"

  // properties - start
  string                  _header;
  bit                     is_zfinx = riscv_instr_pkg::RV32ZFINX inside {riscv_instr_pkg::supported_isa};;
  bit                     is_fp_instr;
  riscv_instr_name_t      include_instr[];
  riscv_instr_name_t      exclude_instr[];
  riscv_instr_group_t     include_group[];
  bit                     use_fp_only_for_directed_instr;     // use fp instr only as directed instrs in stream
  bit                     use_no_repetitive_instr_per_stream; // directed instr is not allow in a stream
  bit                     use_same_instr_per_stream;          // same directed is use within a stream
  bit                     use_prev_rd_on_next_operands;       // previous instr rd is used for directed instr operands
  bit                     more_weight_for_fdiv_fsqrt_gen;     // more weight on generating fdiv and fsqrt directed_instr
  bit                     temp_exclude_fdiv_fsqrt;

    // for use_prev_rd_on_next_operands implementation usage - start
  riscv_reg_t                 prev_rd;
  riscv_fpr_t                 prev_fd;
  bit                         prev_has_rd_detected, prev_has_fd_detected;
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
    if (use_no_repetitive_instr_per_stream) {
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
      soft avail_gp_regs[i][0] inside {[S0:A5]}; // MUST: RV32C only uses 8 most common regs
      soft avail_gp_regs[i][1] inside {SP};      // MUST: some random instr uses SP as rd
      foreach (avail_gp_regs[i][j]) {
        !(avail_gp_regs[i][j] inside {cfg.reserved_regs, reserved_rd});
      }
    }
  }

  constraint c_avail_fp_regs {
    soft avail_fp_regs.size() == num_of_instr_per_stream;
    foreach (avail_fp_regs[i]) {
      soft avail_fp_regs[i].size() > FLEN/2;   // widen the range of selections
      soft avail_fp_regs[i].size() < FLEN + 1; // total of available fpr
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
    use_fp_only_for_directed_instr      = 1; // directed instr is fp only
    use_prev_rd_on_next_operands        = 0;
    use_no_repetitive_instr_per_stream  = 0;
    temp_exclude_fdiv_fsqrt             = 1; // excliude these instr from directed instr
  endfunction: pre_randomize

  function void post_randomize();
    riscv_instr                 instr;
    riscv_fp_in_x_regs_instr    instr_zfinx;
    riscv_floating_point_instr  instr_f;

    `uvm_info(_header, $sformatf(">>%s with following constraints \
      \n>> num_of_instr_per_stream            [%0d] \
      \n>> enable_special_operand_patterns    [%0b] \
      \n>> use_fp_only_for_directed_instr     [%0b] \
      \n>> use_no_repetitive_instr_per_stream [%0b] \
      \n>> use_same_instr_per_stream          [%0b] \
      \n>> use_prev_rd_on_next_operands       [%0b] \
      \n>> more_weight_for_fdiv_fsqrt_gen     [%0b] \
      \n>> temp_exclude_fdiv_fsqrt            [%0b] \
      ",
      get_name(), num_of_instr_per_stream, enable_special_operand_patterns, use_fp_only_for_directed_instr, 
      use_no_repetitive_instr_per_stream, use_same_instr_per_stream, use_prev_rd_on_next_operands,
      more_weight_for_fdiv_fsqrt_gen, temp_exclude_fdiv_fsqrt
      ), UVM_NONE);

    if (enable_special_operand_patterns) begin
      foreach (operand_a[i]) begin
        `uvm_info(_header, $sformatf(">> Specific operand patterns \
          \n>> instr[%0d] operand_a is %0d [%s]\
          \n>> instr[%0d] operand_b is %0d [%s]\
          \n>> instr[%0d] operand_c is %0d [%s]\
          \n>>", 
          i, operand_a[i][31:12], operand_a_pattern[i],
          i, operand_b[i][31:12], operand_b_pattern[i],
          i, operand_c[i][31:12], operand_c_pattern[i]), (enable_special_operand_patterns) ? UVM_NONE : UVM_DEBUG);
      end
    end

    for (int i = 0; i < num_of_instr_per_stream; i++) begin : GEN_N_MANIPULATE_INSTR

      // directed instr gen per stream generation
      update_directed_instr_arg_list();
      instr = new riscv_instr::get_rand_instr(
        .include_instr(include_instr),
        .exclude_instr(exclude_instr),
        .include_group(include_group)
      );
      is_fp_instr = (instr.group inside {RV32F, RV32ZFINX});
      update_next_instr(instr, i);
      rand_var_for_inline_constraint();

      // multicycle instr prior directed instr
      insert_mc_instr(instr, i); 

      // directed instr randomization based on extension
      if (!is_fp_instr) begin : OTHER_NON_FP_SUPPORTED_EXTENSIONS
        randomize_gpr(instr);
        if (!(instr.group == RV32C)) f_use_prev_rd_on_next_operands(.p_instr((use_prev_rd_on_next_operands) ? instr : null), .idx(i));
        if (instr.instr_name inside {SB, SH, SW, C_SW, C_SWSP}) begin: SPECIAL_HANDLING_FOR_STORE
          wa_prevent_store_on_code_space(instr);
        end
        instr_list.push_back(instr);
      end
      else if (is_zfinx) begin : EXTENSION_ZFINX
        `DV_CHECK_FATAL($cast(instr_zfinx, instr), "Cast to instr_zfinx failed!");
        randomize_gpr_zfinx(instr_zfinx, i);
        f_use_prev_rd_on_next_operands(.p_instr_zfinx((use_prev_rd_on_next_operands) ? instr_zfinx : null), .idx(i));
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
        f_use_prev_rd_on_next_operands(.p_instr_f((use_prev_rd_on_next_operands) ? instr_f : null), .idx(i));
        if (instr_f.instr_name == FSW) begin: SPECIAL_HANDLING_FOR_STORE
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

      // actions after directed instr
      act_post_directed_instr(i);

    end // for GEN_N_MANIPULATE_INSTR

    super.post_randomize();
  endfunction: post_randomize

  // for updating the arguments that use in get_rand_instr 
  virtual function void update_directed_instr_arg_list();
    include_group = new[1] ((is_zfinx) ? {RV32ZFINX} : {RV32F});
    if (!use_fp_only_for_directed_instr) begin : USE_MIXED_FP_N_OTHERS_INSTR
      bit more_fp_instr, rand_status;
      exclude_instr = new[24];
      exclude_instr = `FP_STREAM_EXCLUDE_LIST;

      if (more_weight_for_fdiv_fsqrt_gen) begin
        include_group = new[5] (`RV_DV_ISA);
      end
      else begin
        // put more weight in generating fp instr in directed streams
        rand_status = std::randomize(more_fp_instr) with {more_fp_instr dist {1:=2, 0:=1};};
        assert(rand_status);
        if (more_fp_instr) begin
          include_group = new[1] ((is_zfinx) ? {RV32ZFINX} : {RV32F});
        end else begin
          include_group = new[3] ({RV32I, RV32M, RV32C}); 
        end // !more_weight_for_fdiv_fsqrt_gen
      end
    end // !use_fp_only_for_directed_instr
    if (temp_exclude_fdiv_fsqrt) exclude_instr = new[exclude_instr.size() + 2] ({exclude_instr, FDIV_S, FSQRT_S});
  endfunction: update_directed_instr_arg_list

  // placeholder for ext class to insert multicycle instrs
  virtual function void insert_mc_instr(riscv_instr instr, int idx=0);
  endfunction : insert_mc_instr

  virtual function void update_next_instr(riscv_instr prev_instr=null, int idx=0);
    if (use_no_repetitive_instr_per_stream && prev_instr != null) begin
      int size = exclude_instr.size();
      exclude_instr       = new[size+1] (exclude_instr);
      exclude_instr[size] = prev_instr.instr_name;
    end
    if (use_same_instr_per_stream && prev_instr != null) begin
      include_instr       = new[1] ({prev_instr.instr_name});
    end
    if (more_weight_for_fdiv_fsqrt_gen) begin
      // at least 50% of the total directed_instr should be either fdiv/fsqrt
      if (idx%2 && !(prev_instr.instr_name inside {FDIV_S, FSQRT_S})) include_instr = new[1] ($urandom_range(1) ? {FDIV_S} : {FSQRT_S});
      else                                                            include_instr.delete();
    end
  endfunction: update_next_instr

  function void randomize_gpr(riscv_instr instr, int idx=0);
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
      rm == local::rm;
      use_rounding_mode_from_instr == local::use_rounding_mode_from_instr;
    )

  endfunction: randomize_gpr

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
      OR :  begin // OR rd rs1 rs2
              `DV_CHECK_RANDOMIZE_WITH_FATAL(instr, 
                rd == local::rd; rs1 == local::rs1; rs2 == local::rs2;
              )
            end
      SRLI : begin // SRLI rd rs1 imm
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

  // for getting random special pattern and setting
  virtual function void get_xreg_val_for_rand_pattern(ref int unsigned rs_unsigned, ref int rs_signed, ref operand_pattens_t pattern);
    unique case ($urandom_range(0,4)) 
      0:  begin // percision max
            rs_unsigned = 16777216; rs_signed = 16777216;
            pattern = W_IS_AT_PERCISION_MAX;
          end
      1:  begin // percision min
            rs_unsigned = 0; rs_signed = -16777216;
            pattern = W_IS_AT_PERCISION_MIN;
          end
      2:  begin // within percision limit
            rs_unsigned = $urandom_range(0, 16777216); 
            rs_signed   = ($urandom_range(1)) ? (int'(rs_unsigned)) : (int'(rs_unsigned) * (-1)); // range from -16777216 till 16777216
            pattern = W_IS_WITHIN_PERCISION_LIMIT;
          end
      3:  begin // max integer
            rs_unsigned = 32'hFFFF_FFFF; rs_signed = 32'h7FFF_FFFF;
            pattern = W_IS_MAX_INTEGER;
          end
      4:  begin // min integer
            rs_unsigned = 32'h0; rs_signed = 32'h8000_0000;
            pattern = W_IS_MIN_INTEGER;
          end
    endcase
  endfunction : get_xreg_val_for_rand_pattern

  // for manipulating zfinx instr operands
  virtual function void manipulate_zfinx_instr_operands(riscv_fp_in_x_regs_instr instr=null, int idx=0);

    bit [31:0]        m_operand_a, m_operand_b, m_operand_c;
    operand_pattens_t m_operand_a_pattern, m_operand_b_pattern, m_operand_c_pattern;
    riscv_reg_t       mem_rd, imm_rd, imm_rd2;

    if (
      instr.has_rs1 && operand_a_pattern[idx] != IS_RAND ||
      instr.has_rs2 && operand_b_pattern[idx] != IS_RAND ||
      instr.has_rs3 && operand_c_pattern[idx] != IS_RAND ||
      (instr.instr_name inside {FCVT_S_W, FCVT_S_WU})
    ) begin : DEFINE_MEM_ADDR
      riscv_instr m_instr;

      void'(std::randomize(mem_rd)  with {!(mem_rd  inside {cfg.reserved_regs, reserved_rd, instr.rs1, instr.rs2, instr.rs3, instr.rd, ZERO});          });
      void'(std::randomize(imm_rd)  with {!(imm_rd  inside {cfg.reserved_regs, reserved_rd, instr.rs1, instr.rs2, instr.rs3, instr.rd, ZERO, mem_rd});  });
      // fixme
      // void'(std::randomize(imm_rd2) with {!(imm_rd2 inside {cfg.reserved_regs, reserved_rd, instr.rs1, instr.rs2, instr.rs3, instr.rd, ZERO, mem_rd, imm_rd});  });
      if ( 
        (instr.has_rs1 && operand_a_pattern[idx] inside `FP_SPECIAL_OPERANDS_LIST_2) ||
        (instr.has_rs2 && operand_b_pattern[idx] inside `FP_SPECIAL_OPERANDS_LIST_2) ||
        (instr.has_rs3 && operand_c_pattern[idx] inside `FP_SPECIAL_OPERANDS_LIST_2) ||
        (instr.instr_name inside {FCVT_S_W, FCVT_S_WU})
      ) begin
        void'(std::randomize(imm_rd2) with {!(imm_rd2 inside {cfg.reserved_regs, reserved_rd, instr.rs1, instr.rs2, instr.rs3, instr.rd, ZERO, mem_rd, imm_rd});  });
        //void'(std::randomize(imm_rd2) with {
        //  if (instr.has_rs1) {!(imm_rd2 inside {cfg.reserved_regs, reserved_rd, instr.rs1, ZERO, mem_rd, imm_rd});  }
        //  if (instr.has_rs2) {!(imm_rd2 inside {cfg.reserved_regs, reserved_rd, instr.rs2, ZERO, mem_rd, imm_rd});  }
        //  if (instr.has_rs3) {!(imm_rd2 inside {cfg.reserved_regs, reserved_rd, instr.rs3, ZERO, mem_rd, imm_rd});  }
        //  if (instr.has_rd)  {!(imm_rd2 inside {cfg.reserved_regs, reserved_rd, instr.rd,  ZERO, mem_rd, imm_rd});  }
        //});
      end

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

    if (!(instr.instr_name inside {FCVT_S_W, FCVT_S_WU})) begin
      if      (m_operand_a_pattern inside `FP_SPECIAL_OPERANDS_LIST_1) begin `MANIPULATE_GPR_OPERANDS_UPPER_20BITS_ONLY(rs1,m_operand_a) end
      else if (m_operand_a_pattern inside `FP_SPECIAL_OPERANDS_LIST_2) begin `MANIPULATE_GPR_OPERANDS_WORD(rs1,m_operand_a) end
      else if (m_operand_a_pattern != IS_RAND) begin `uvm_fatal(_header, $sformatf("[manipulate_zfinx_instr_operands] Invalid m_operand_a_pattern[%s]", m_operand_a_pattern.name())); end
      if      (m_operand_b_pattern inside `FP_SPECIAL_OPERANDS_LIST_1) begin `MANIPULATE_GPR_OPERANDS_UPPER_20BITS_ONLY(rs2,m_operand_b) end
      else if (m_operand_b_pattern inside `FP_SPECIAL_OPERANDS_LIST_2) begin `MANIPULATE_GPR_OPERANDS_WORD(rs2,m_operand_b) end
      else if (m_operand_b_pattern != IS_RAND) begin `uvm_fatal(_header, $sformatf("[manipulate_zfinx_instr_operands] Invalid m_operand_b_pattern[%s]", m_operand_b_pattern.name())); end
      if      (m_operand_c_pattern inside `FP_SPECIAL_OPERANDS_LIST_1) begin `MANIPULATE_GPR_OPERANDS_UPPER_20BITS_ONLY(rs3,m_operand_c) end
      else if (m_operand_c_pattern inside `FP_SPECIAL_OPERANDS_LIST_2) begin `MANIPULATE_GPR_OPERANDS_WORD(rs3,m_operand_c) end
      else if (m_operand_c_pattern != IS_RAND) begin `uvm_fatal(_header, $sformatf("[manipulate_zfinx_instr_operands] Invalid m_operand_c_pattern[%s]", m_operand_c_pattern.name())); end
    end
    else begin : FOR_CVT_FROM_INT_TO_FP
      if (instr.has_rs1 && operand_a_pattern[idx] != IS_RAND) begin
        int unsigned rs1_unsigned;
        int          rs1_signed;
        get_xreg_val_for_rand_pattern(
          .rs_unsigned  (rs1_unsigned),
          .rs_signed    (rs1_signed),
          .pattern      (m_operand_a_pattern)
        );
        if (instr.instr_name == FCVT_S_WU) m_operand_a = rs1_unsigned;
        else                               m_operand_a = rs1_signed;
        if (m_operand_a_pattern inside {W_IS_AT_PERCISION_MAX, W_IS_AT_PERCISION_MIN, W_IS_MIN_INTEGER}) begin 
          `MANIPULATE_GPR_OPERANDS_UPPER_20BITS_ONLY(rs1, m_operand_a); 
        end else begin : W_IS_WITHIN_PERCISION_LIMIT_OR_W_IS_MAX_INTEGER
          `MANIPULATE_GPR_OPERANDS_WORD(rs1, m_operand_a);
        end
      end
    end // FOR_CVT_FROM_INT_TO_FP
    
  endfunction: manipulate_zfinx_instr_operands
 
  // for manipulating f instr operands
  virtual function void manipulate_f_instr_operands(riscv_floating_point_instr instr=null, int idx=0);

    bit [31:0]        m_operand_a, m_operand_b, m_operand_c;
    operand_pattens_t m_operand_a_pattern, m_operand_b_pattern, m_operand_c_pattern;
    riscv_reg_t       mem_rd, imm_rd, imm_rd2;

    if (
      instr.has_fs1 && operand_a_pattern[idx] != IS_RAND ||
      instr.has_fs2 && operand_b_pattern[idx] != IS_RAND ||
      instr.has_fs3 && operand_c_pattern[idx] != IS_RAND ||
      (instr.instr_name inside {FCVT_S_W, FCVT_S_WU})
    ) begin : DEFINE_MEM_ADDR
      riscv_instr m_instr;

      void'(std::randomize(mem_rd)  with {!(mem_rd  inside {cfg.reserved_regs, reserved_rd, instr.rs1, instr.rs2, instr.rd, ZERO});        });
      void'(std::randomize(imm_rd)  with {!(imm_rd  inside {cfg.reserved_regs, reserved_rd, instr.rs1, instr.rs2, instr.rd, ZERO, mem_rd});  });
      // fixme
      // void'(std::randomize(mem_rd) with {
      //   if (instr.has_rs1) { !(mem_rd inside {cfg.reserved_regs, reserved_rd, ZERO, instr.rs1});  }
      //   if (instr.has_rd)  { !(mem_rd inside {cfg.reserved_regs, reserved_rd, ZERO, instr.rd});   }
      // });
      // void'(std::randomize(imm_rd) with {
      //   if (instr.has_rs1) { !(imm_rd inside {cfg.reserved_regs, reserved_rd, ZERO, instr.rs1, mem_rd});  }
      //   if (instr.has_rd)  { !(imm_rd inside {cfg.reserved_regs, reserved_rd, ZERO, instr.rd,  mem_rd});  }
      // });
      if ( 
        (instr.has_fs1 && operand_a_pattern[idx] inside `FP_SPECIAL_OPERANDS_LIST_2) ||
        (instr.has_fs2 && operand_b_pattern[idx] inside `FP_SPECIAL_OPERANDS_LIST_2) ||
        (instr.has_fs3 && operand_c_pattern[idx] inside `FP_SPECIAL_OPERANDS_LIST_2) ||
        (instr.instr_name inside {FCVT_S_W, FCVT_S_WU})
      ) begin
        void'(std::randomize(imm_rd2) with {!(imm_rd2 inside {cfg.reserved_regs, reserved_rd, instr.rs1, instr.rs2, instr.rd, ZERO, mem_rd, imm_rd});  });
        // void'(std::randomize(imm_rd2) with {
        //   if (instr.has_rs1) { !(imm_rd2 inside {cfg.reserved_regs, reserved_rd, instr.rs1, mem_rd, imm_rd});  }
        //   if (instr.has_rd)  { !(imm_rd2 inside {cfg.reserved_regs, reserved_rd, instr.rd,  mem_rd, imm_rd});  }
        // });
      end

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

    if (!(instr.instr_name inside {FCVT_S_W, FCVT_S_WU})) begin
      if      (m_operand_a_pattern inside `FP_SPECIAL_OPERANDS_LIST_1) begin `MANIPULATE_FPR_OPERANDS_UPPER_20BITS_ONLY(fs1,m_operand_a) end
      else if (m_operand_a_pattern inside `FP_SPECIAL_OPERANDS_LIST_2) begin `MANIPULATE_FPR_OPERANDS_WORD(fs1,m_operand_a) end
      else if (m_operand_a_pattern != IS_RAND) begin `uvm_fatal(_header, $sformatf("[manipulate_f_instr_operands] Invalid m_operand_a_pattern[%s]", m_operand_a_pattern.name())); end
      if      (m_operand_b_pattern inside `FP_SPECIAL_OPERANDS_LIST_1) begin `MANIPULATE_FPR_OPERANDS_UPPER_20BITS_ONLY(fs2,m_operand_b) end
      else if (m_operand_b_pattern inside `FP_SPECIAL_OPERANDS_LIST_2) begin `MANIPULATE_FPR_OPERANDS_WORD(fs2,m_operand_b) end
      else if (m_operand_b_pattern != IS_RAND) begin `uvm_fatal(_header, $sformatf("[manipulate_f_instr_operands] Invalid m_operand_b_pattern[%s]", m_operand_b_pattern.name())); end
      if      (m_operand_c_pattern inside `FP_SPECIAL_OPERANDS_LIST_1) begin `MANIPULATE_FPR_OPERANDS_UPPER_20BITS_ONLY(fs3,m_operand_c) end
      else if (m_operand_c_pattern inside `FP_SPECIAL_OPERANDS_LIST_2) begin `MANIPULATE_FPR_OPERANDS_WORD(fs3,m_operand_c) end
      else if (m_operand_c_pattern != IS_RAND) begin `uvm_fatal(_header, $sformatf("[manipulate_f_instr_operands] Invalid m_operand_c_pattern[%s]", m_operand_c_pattern.name())); end
    end
    else begin : FOR_CVT_FROM_INT_TO_FP
      if (instr.has_rs1 && operand_a_pattern[idx] != IS_RAND) begin
        int unsigned rs1_unsigned;
        int          rs1_signed;
        get_xreg_val_for_rand_pattern(
          .rs_unsigned  (rs1_unsigned),
          .rs_signed    (rs1_signed),
          .pattern      (m_operand_a_pattern)
        );
        if (instr.instr_name == FCVT_S_WU) m_operand_a = rs1_unsigned;
        else                               m_operand_a = rs1_signed;
        if (m_operand_a_pattern inside {W_IS_AT_PERCISION_MAX, W_IS_AT_PERCISION_MIN, W_IS_MIN_INTEGER}) begin 
          `MANIPULATE_GPR_OPERANDS_UPPER_20BITS_ONLY(rs1, m_operand_a); 
        end else begin : W_IS_WITHIN_PERCISION_LIMIT_OR_W_IS_MAX_INTEGER
          `MANIPULATE_GPR_OPERANDS_WORD(rs1, m_operand_a);
        end
      end
    end // FOR_CVT_FROM_INT_TO_FP
    
  endfunction: manipulate_f_instr_operands

  // placeholder for post actions after directed instr
  virtual function void act_post_directed_instr(int idx=0);
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
        (p_instr_zfinx != null && p_instr != null) ||
        (p_instr_f != null     && p_instr != null)
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

    // if (prev_has_r_flags[0]) begin : PREV_HAS_RD
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
            (curr_has_r_flags[rand_idx] && p_instr != null)
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

    // else if (prev_has_f_flags[0]) begin : PREV_HAS_FD
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
                                       ((p_instr_f != null) ? p_instr_f.rd : p_instr.rd); 
    if (curr_has_f_flags[0]) prev_fd = p_instr_f.fd;

    prev_has_r_flags = curr_has_r_flags;
    prev_has_f_flags = curr_has_f_flags;
    if (prev_has_r_flags[0]) prev_has_rd_detected = 1;
    if (prev_has_f_flags[0]) prev_has_fd_detected = 1;

    end // FUNC_BODY

  endfunction: f_use_prev_rd_on_next_operands

  // workaround to prevent FSW from overriding onto the code space
  virtual function void wa_prevent_store_on_code_space(riscv_instr instr, int idx=0);

    bit [7:0]                   wa_rand_imm = $urandom_range(1,255);
    riscv_instr                 wa_instr;
    riscv_floating_point_instr  _instr;
    riscv_reg_t                 rd;

    if (is_fp_instr) begin
      `DV_CHECK_FATAL($cast(_instr, instr), "Cast to _instr failed!");
    end
    if (instr.instr_name == C_SWSP) rd = SP;
    else                            rd = (is_fp_instr) ? _instr.rs1 : instr.rs1;

    wa_instr = new riscv_instr::get_rand_instr(.include_instr({LUI}));
    override_instr(
      .instr  (wa_instr),
      .rd     (rd),
      .imm    ({12'h0, wa_rand_imm, 12'h0}) // yyy_ww_xxx
    );
    instr_list.push_back(wa_instr);
    instr_list[$].comment = {instr_list[$].comment, $sformatf(" [wa_prevent_store_on_code_space] ")};

  endfunction: wa_prevent_store_on_code_space

endclass: cv32e40p_float_zfinx_base_instr_stream


  //
  // extended class that having mixed of others and fp directed_instrs within a stream
  // fp instr generation has more weightage than others isa
  // note: these are default classes that use to cover all the verif plan requirements
  // note: 3 variants: with/without specific fdiv/fsqrt exclusion, more_weight_for_fdiv_fsqrt_gen
class cv32e40p_fp_n_mixed_instr_stream extends cv32e40p_float_zfinx_base_instr_stream;

  `uvm_object_utils(cv32e40p_fp_n_mixed_instr_stream)
  `uvm_object_new

  function void pre_randomize();
    super.pre_randomize();
    use_fp_only_for_directed_instr = 0; // directed instr is mixtured of supported isa
    temp_exclude_fdiv_fsqrt        = 0;
  endfunction: pre_randomize

endclass: cv32e40p_fp_n_mixed_instr_stream
class cv32e40p_fp_n_mixed_instr_w_excl_stream extends cv32e40p_float_zfinx_base_instr_stream;

  `uvm_object_utils(cv32e40p_fp_n_mixed_instr_w_excl_stream)
  `uvm_object_new

  function void pre_randomize();
    super.pre_randomize();
    use_fp_only_for_directed_instr = 0; // directed instr is mixtured of supported isa
    temp_exclude_fdiv_fsqrt        = 1; // excliude these instr from directed instr
    assert (!more_weight_for_fdiv_fsqrt_gen && temp_exclude_fdiv_fsqrt);
  endfunction: pre_randomize

endclass: cv32e40p_fp_n_mixed_instr_w_excl_stream
class cv32e40p_fp_n_mixed_instr_more_fdiv_fsqrt_stream extends cv32e40p_float_zfinx_base_instr_stream;

  `uvm_object_utils(cv32e40p_fp_n_mixed_instr_more_fdiv_fsqrt_stream)
  `uvm_object_new

  function void pre_randomize();
    super.pre_randomize();
    use_fp_only_for_directed_instr = 0; // directed instr is mixtured of supported isa
    temp_exclude_fdiv_fsqrt        = 0;
    more_weight_for_fdiv_fsqrt_gen = 1;
    assert (!temp_exclude_fdiv_fsqrt && more_weight_for_fdiv_fsqrt_gen);
  endfunction: pre_randomize

endclass: cv32e40p_fp_n_mixed_instr_more_fdiv_fsqrt_stream

  //
  // extended class that use to override instr operands with specific patterns
class cv32e40p_fp_w_special_operands_instr_stream extends cv32e40p_float_zfinx_base_instr_stream;

  `uvm_object_utils(cv32e40p_fp_w_special_operands_instr_stream)
  `uvm_object_new

  constraint ovr_c_others {
    num_of_instr_per_stream == 15; // fixed
  }

  constraint ovr_c_enable_special_operand_patterns {
    enable_special_operand_patterns == 1;
  }

  function void pre_randomize();
    super.pre_randomize();
    use_fp_only_for_directed_instr = 1;
  endfunction: pre_randomize

  // to define exclude list for this stream class
  virtual function void update_directed_instr_arg_list();
    super.update_directed_instr_arg_list();
    // exclude FLW, FSW and FMV_W_X: no fp regs as operand and by refering to verif plan
    exclude_instr = new[exclude_instr.size() + 2] ({exclude_instr, FLW, FSW});
    // note: should test all rather just focus on specific instrs as per verifplan. although others are covered in onespin?
    //TBD if (!use_no_repetitive_instr_per_stream && !use_same_instr_per_stream) begin
    //TBD   exclude_instr = new[exclude_instr.size() + 12] (
    //TBD     {exclude_instr, FADD_S, FSUB_S, FMIN_S, FMAX_S, FSGNJ_S, FSGNJN_S, FSGNJX_S, FMV_W_X, FEQ_S, FLT_S, FLE_S, FCLASS_S});
    //TBD end
  endfunction: update_directed_instr_arg_list

endclass: cv32e40p_fp_w_special_operands_instr_stream

  //
  // extended class that use to override current directed_instr operands with previous rd/fd (previous does not mean in b2b instr manner)
  // note: this is additional class that use to improve the coverage defined in verif plan
class cv32e40p_fp_w_prev_rd_as_operand_instr_stream extends cv32e40p_float_zfinx_base_instr_stream;

  `uvm_object_utils(cv32e40p_fp_w_prev_rd_as_operand_instr_stream)
  `uvm_object_new

  function void pre_randomize();
    super.pre_randomize();
    use_prev_rd_on_next_operands   = 1;
    use_fp_only_for_directed_instr = 0;
  endfunction: pre_randomize

  // to define exclude list for this stream class
  virtual function void update_directed_instr_arg_list();
    super.update_directed_instr_arg_list();
    // exclude FSW: rs1/offset need to prevent from overriding the code space; rs1 should not overriden by prev rd
    exclude_instr = new[exclude_instr.size() + 1] ({exclude_instr, FSW});
  endfunction: update_directed_instr_arg_list

endclass: cv32e40p_fp_w_prev_rd_as_operand_instr_stream

// fixme: new class to stress test operand forwarding
// info: https://en.wikipedia.org/wiki/Operand_forwarding

  // [optional] extended class that preceeded mc instr prior directed fp instr
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

  function void pre_randomize();
    super.pre_randomize();
    // cycle through all possible mc instrs for selected directed fp instr per stream
    use_fp_only_for_directed_instr = 1;
    use_same_instr_per_stream      = 1;
    assert (use_fp_only_for_directed_instr && use_same_instr_per_stream);
  endfunction: pre_randomize

  constraint ovr_c_others {
    // FIXME_TEMP_EXCLUDE_UNTIL_RTL_IS_FIXED (-2)
    if (is_zfinx) {num_of_instr_per_stream == TOTAL_INSTR_ZFINX_TYPE - 2;}
    else          {num_of_instr_per_stream == TOTAL_INSTR_F_TYPE - 2;}
  }

  virtual function void act_post_directed_instr(int idx=0);
    // put some random NOP before next mc fp iteration
    insert_nop_instr($urandom_range(2,3));
  endfunction: act_post_directed_instr

  // stream implementation to insert mc fp instr
  virtual function void insert_mc_instr(riscv_instr instr, int idx=0);

    riscv_instr                 mc_instr;
    riscv_fp_in_x_regs_instr    mc_instr_zfinx;
    riscv_floating_point_instr  mc_instr_f;

    if (instr.group inside {RV32F, RV32ZFINX}) begin : BODY

      mc_instr = new riscv_instr::get_rand_instr(
        // FIXME_TEMP_EXCLUDE_UNTIL_RTL_IS_FIXED (fdiv and fsqrt)
        .exclude_instr({mc_exclude_instr, FDIV_S, FSQRT_S}),
        // .exclude_instr(mc_exclude_instr),
        .include_group((is_zfinx) ? {RV32ZFINX} : {RV32F})
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
        if (mc_instr_f.instr_name inside {FSW, SB, SH, SW}) begin: SPECIAL_HANDLING_FOR_FLW
          wa_prevent_store_on_code_space(mc_instr_f);
        end
        update_mc_instr_latency(mc_instr_f);
        instr_list.push_back(mc_instr_f);
      end
      instr_list[$].comment = {instr_list[$].comment, $sformatf(" [insert_mc_instr] ")};

      rand_fill_mc_latency_w_instrs( .instr_zfinx(mc_instr_zfinx), .instr_f(mc_instr_f) );

    end // BODY

  endfunction : insert_mc_instr

  // for cycle through all posible mc instr
  virtual function void update_next_mc_instr(riscv_instr prev_instr=null);
    if (prev_instr != null) begin
      int size = mc_exclude_instr.size();
      // FIXME_TEMP_EXCLUDE_UNTIL_RTL_IS_FIXED (fdiv and fsqrt)
      mc_exclude_instr       = new[size+1+2] ({mc_exclude_instr, FDIV_S, FSQRT_S});
      // mc_exclude_instr       = new[size+1] (mc_exclude_instr);
      mc_exclude_instr[size] = prev_instr.instr_name;
    end
  endfunction: update_next_mc_instr

  // to update mc instr latency
  virtual function void update_mc_instr_latency(riscv_instr mc_instr=null);

    unique case(mc_instr.instr_name)
      FLW, FSW:                   begin mc_instr_latency = 2; end
      FMV_W_X, FMV_X_W:           begin mc_instr_latency = 2; end
      FMADD_S, FMSUB_S:           begin mc_instr_latency = 1 + fpu_addmul_lat; end
      FNMSUB_S, FNMADD_S:         begin mc_instr_latency = 1 + fpu_addmul_lat; end
      FADD_S, FSUB_S:             begin mc_instr_latency = 1 + fpu_addmul_lat; end
      FMUL_S:                     begin mc_instr_latency = 1 + fpu_addmul_lat; end
      FMIN_S, FMAX_S:             begin mc_instr_latency = 1 + fpu_addmul_lat; end
      FDIV_S, FSQRT_S:            begin mc_instr_latency = $urandom_range(1,12); end
      FSGNJ_S,FSGNJN_S, FSGNJX_S: begin mc_instr_latency = 1 + fpu_others_lat; end
      FCVT_W_S, FCVT_WU_S:        begin mc_instr_latency = 1 + fpu_others_lat; end
      FEQ_S, FLT_S, FLE_S:        begin mc_instr_latency = 1 + fpu_others_lat; end
      FCLASS_S:                   begin mc_instr_latency = 1 + fpu_others_lat; end
      FCVT_S_W,FCVT_S_WU:         begin mc_instr_latency = 1 + fpu_others_lat; end
    endcase

  endfunction: update_mc_instr_latency

  // to fill up mc latency period with random instr
  // to delay the directed_instr insertion with deterministic delay
  virtual function void rand_fill_mc_latency_w_instrs(
    riscv_fp_in_x_regs_instr    instr_zfinx=null,
    riscv_floating_point_instr  instr_f=null
  );

    riscv_instr   rand_instr;
    int           rand_instr_latency;
    int           rand_mc_latency = $urandom_range(0,mc_instr_latency);
    int           loop_cnt = 0;

    assert(rand_mc_latency >= 0);

    while (!(loop_cnt == 100) && rand_mc_latency > 0) begin
      int p_rand_mc_latency = rand_mc_latency;
      bit skip = 0;
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
              if ((rand_mc_latency - 5) < 0) 
                skip = 1;
              else
                rand_mc_latency = rand_mc_latency - 5; // determistic
            end
      endcase
      if (!skip) begin
        // fillng_instr need to have no rd/rs dependency on fp instr so that pipeline can go through
        reserved_rd.delete();
        if (is_zfinx) begin
          if (instr_zfinx.has_rs1) begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr_zfinx.rs1}); end
          if (instr_zfinx.has_rs2) begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr_zfinx.rs2}); end
          if (instr_zfinx.has_rs3) begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr_zfinx.rs3}); end
          if (instr_zfinx.has_rd)  begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr_zfinx.rd}); end
        end else begin
          if (instr_f.has_rs1) begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr_f.rs1}); end
          if (instr_f.has_rs2) begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr_f.rs2}); end
          if (instr_f.has_rd)  begin reserved_rd = new[reserved_rd.size() + 1] ({reserved_rd, instr_f.rd}); end
        end
        randomize_gpr(rand_instr);
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


// ALL FP STREAM CLASSESS - end
