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

// DEFINES used in this class - start
  // constraint for special pattern operands
  // fixme: update the weight again
  // note: DONOT insert " solve enable_special_operand_patterns before operand_``IDX``_pattern;\" at below code, it will limit the constraints (havent root caused)
  `define C_OPERAND_PATTERN(IDX) \
    constraint c_operand_``IDX``_pattern {\
      soft operand_``IDX``_pattern.size() == num_of_instr_per_stream;\
      foreach (operand_``IDX``_pattern[i]) {\
        if (enable_special_operand_patterns) {\
          operand_``IDX``_pattern[i] dist { IS_RAND := 4, IS_Q_NAN  := 2, IS_S_NAN              := 2, \
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
// 1) fcvt.s.w - understand this and update for above

// ALL FP STREAM CLASSESS - start
  // base class for fp instruction stream generation
class cv32e40p_float_zfinx_base_instr_stream extends cv32e40p_base_instr_stream;

  localparam TOTAL_FPR = 32;

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
  string              _header;
  bit                 is_zfinx;
  riscv_instr_name_t  include_instr[];
  riscv_instr_name_t  exclude_instr[];
  bit                 use_diff_instr_per_stream; // fixme: pending implementation
  bit                 use_same_regs_for_operands_per_stream; // fixme: pending implementation

    // fixme: add constraints for multicycle instr 
    // some instr will become multicycle if below properties are not-0
  `ifdef FPU_ADDMUL_LAT
    int unsigned fpu_addmul_lat = `FPU_ADDMUL_LAT;
  `else
    int unsigned fpu_addmul_lat = 0;
  `endif
  `ifdef FPU_OTHERS_LAT
    int unsigned fpu_others_lat = `FPU_OTHERS_LAT;
  `else
    int unsigned fpu_others_lat = 0;
  `endif

  rand int unsigned       num_of_instr_per_stream;
  rand riscv_reg_t        avail_gp_regs[][];  // for zfinx and f
  rand riscv_fpr_t        avail_fp_regs[][];  // for f only
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
    soft num_of_instr_per_stream == 30; // fixed to 30
    num_of_instr_per_stream > 0;
    // soft num_of_instr_per_stream inside {[10:15]};
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

  function new (string name="");
    super.new(name);
    _header = this.type_name;
    if ( !(riscv_instr_pkg::RV32ZFINX inside {riscv_instr_pkg::supported_isa}) && ! (riscv_instr_pkg::RV32F inside {riscv_instr_pkg::supported_isa}) ) begin
      `uvm_error(_header, $sformatf("RV32ZFINX and RV32F are not defined in RV_DV_ISA - refer cv32e40p_supported_isa.svh"));
    end
    is_zfinx = riscv_instr_pkg::RV32ZFINX inside {riscv_instr_pkg::supported_isa};
  endfunction: new

  function void pre_randomize();
    super.pre_randomize();
  endfunction: pre_randomize

  function void post_randomize();
    riscv_instr                 instr;
    riscv_fp_in_x_regs_instr    instr_zfinx;
    riscv_floating_point_instr  instr_f;
    riscv_instr_group_t         include_group[] = (is_zfinx)    ? {RV32ZFINX} : 
                                                  ((XLEN >= 64) ? {RV32F, RV64F} : {RV32F});

    `uvm_info(_header, $sformatf("%s - num_of_instr_per_stream[%0d] - enable_special_operand_patterns[%0b]", 
      get_name(), num_of_instr_per_stream, enable_special_operand_patterns), UVM_NONE);
    if (enable_special_operand_patterns) begin
      foreach (operand_a[i]) begin
        `uvm_info(_header, $sformatf(" imm20 for specific operand patterns \
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

      // gnerate instr per stream
      update_get_directed_instr_arg_list();
      instr = new riscv_instr::get_rand_instr(
        .include_instr(include_instr),
        .exclude_instr(exclude_instr),
        .include_group(include_group)
      );
      rand_var_for_inline_constraint();

      // differentiate based on extension
      if (is_zfinx) begin : EXTENSION_ZFINX
        `DV_CHECK_FATAL($cast(instr_zfinx, instr), "Cast to instr_zfinx failed!");
        randomize_gpr_zfinx(instr_zfinx, i);
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
        if (instr_f.instr_name == FSW) begin: SPECIAL_HANDLING_FOR_FLW
          wa_prevent_store_on_code_space(instr_f);
        end
        if (enable_special_operand_patterns) begin : OVERRIDE_OPERANDS_W_SPECIAL_PATTERNS
          if (!(instr_f.instr_name inside {FLW, FSW, FMV_X_W, FMV_W_X})) begin
            manipulate_f_instr_operands(instr_f, i);
          end
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

    end // GEN_N_MANIPULATE_INSTR
    super.post_randomize();
  endfunction: post_randomize

  // to update the arguments that use in get_rand_instr 
  // note: include_group is not allow to be used here, it is fixed in the base class
  virtual function void update_get_directed_instr_arg_list();
    include_instr.delete();
    exclude_instr.delete();
    // fixme: for testing, TBD
    // include_instr = new[1];
    // include_instr[0] = FMADD_S;
    // include_instr[1] = FLW;
    // include_instr = {FSW, FLW};
    // include_instr = {FMADD_S, FMSUB_S};
  endfunction: update_get_directed_instr_arg_list

  // randomize registers to be used in this instr
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

  function void randomize_fpr(riscv_floating_point_instr instr, int idx=0);
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

  function void rand_var_for_inline_constraint();
    // use different <var> for every instr under same stream
    void'(std::randomize(imm));
    void'(std::randomize(rm));
    void'(std::randomize(use_rounding_mode_from_instr));
  endfunction: rand_var_for_inline_constraint

  function void override_instr(
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


  function void manipulate_zfinx_instr_operands(riscv_fp_in_x_regs_instr instr, int idx=0);

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
 

  function void manipulate_f_instr_operands(riscv_floating_point_instr instr, int idx=0);

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


  // workaround to prevent FSW from overriding onto the code space
  function void wa_prevent_store_on_code_space(riscv_floating_point_instr instr, int idx=0);

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


  // extended class that use to override instr operands with specific patterns
class cv32e40p_fp_w_special_operands_instr_stream extends cv32e40p_float_zfinx_base_instr_stream;

  `uvm_object_utils(cv32e40p_fp_w_special_operands_instr_stream)

  constraint ovr_c_others {
    num_of_instr_per_stream == 10; // fixed to 10
    // num_of_instr_per_stream inside {[5:10]};
    solve num_of_instr_per_stream before enable_special_operand_patterns;
  }

  constraint ovr_c_enable_special_operand_patterns {
    enable_special_operand_patterns == 1;
  }

  function new (string name="");
    super.new(name);
  endfunction: new

  function void post_randomize();
    super.post_randomize();
  endfunction: post_randomize

  virtual function void update_get_directed_instr_arg_list();
    // fixme: for testing, TBD
    // include_instr = new[1];
    // include_instr[0] = FMSUB_S;

    // following list is created by referring to the testplan CV32E40P_F-Zfinx-instructions.xls
    exclude_instr = new[15];
    exclude_instr = {FLW, FSW, FADD_S, FSUB_S, FMIN_S, FMAX_S, FSGNJ_S, FSGNJN_S, FSGNJX_S, FMV_X_W, FMV_W_X, FEQ_S, FLT_S, FLE_S, FCLASS_S};
  endfunction: update_get_directed_instr_arg_list

endclass: cv32e40p_fp_w_special_operands_instr_stream

// ALL FP STREAM CLASSESS - end
