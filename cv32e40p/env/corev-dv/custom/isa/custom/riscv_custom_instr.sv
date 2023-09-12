/*
 * Copyright 2019 Google LLC
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


class cv32e40p_instr extends riscv_instr;

  // additionnal helper fields
  bit is_post_incr;
  bit is_r_format ;

  bit hw_loop_label;

  static cv32e40p_instr         cv32e40p_instr_template[riscv_instr_name_t];

  // All derived instructions
  `uvm_object_utils(cv32e40p_instr)
  `uvm_object_new

  static function cv32e40p_instr create_instr(riscv_instr_name_t instr_name);
    uvm_object obj;
    cv32e40p_instr inst;
    string instr_class_name;
    uvm_coreservice_t coreservice = uvm_coreservice_t::get();
    uvm_factory factory = coreservice.get_factory();
    instr_class_name = {"riscv_", instr_name.name(), "_instr"};
    obj = factory.create_object_by_name(instr_class_name, "cv32e40p_instr", instr_class_name);
    if (obj == null) begin
      `uvm_fatal("cv32e40p_instr", $sformatf("Failed to create instr: %0s", instr_class_name))
    end
    if (!$cast(inst, obj)) begin
      `uvm_fatal("cv32e40p_instr", $sformatf("Failed to cast instr: %0s", instr_class_name))
    end
    return inst;
  endfunction : create_instr

  static function cv32e40p_instr get_xpulp_instr( riscv_instr_name_t include_instr[$] = {},
                                                riscv_instr_name_t exclude_instr[$] = {},
                                                riscv_instr_category_t include_category[$] = {},
                                                riscv_instr_category_t exclude_category[$] = {});

    // do this to manage list of unsupported instruction that is somehow not managed in parent class
    riscv_instr_name_t disallowed_instr [$] = { unsupported_instr, exclude_instr };
    riscv_instr_name_t valid_instr[$];
    riscv_instr instr;
    cv32e40p_instr cv32_instr;

    instr = riscv_instr::type_id::create();
    cv32_instr = cv32e40p_instr::type_id::create();

    // if a specific instruction list is wanted, return it along with exclusions
    if (include_instr.size() > 0) begin
      // we create an intersect with given instruction and available RV32X instruction, to make sure
      // non-X instructions has not sneaked-in
      valid_instr = include_instr.find with (item inside { instr_group[RV32X] });
      instr = riscv_instr::get_rand_instr(
        .include_instr    ( valid_instr      ) ,
        .exclude_instr    ( disallowed_instr ) ,
        .exclude_category ( exclude_category )
      );

      $cast(cv32_instr,instr);
      return cv32_instr;
    end

    // if a specific instruction category is wanted, return it along with exclusions
    if (include_category.size() > 0) begin
      // we create an intersect with given instruction and available RV32X instruction, to make sure
      // non-X instructions has not sneaked-in
      foreach (include_category[i]) begin
        valid_instr = { valid_instr, instr_category[include_category[i]].find with (item inside { instr_group[RV32X] }) } ;
      end
      instr = riscv_instr::get_rand_instr (
        .include_instr    ( valid_instr      ) ,
        .exclude_instr    ( disallowed_instr ) ,
        .exclude_category ( exclude_category )
      );

      $cast(cv32_instr,instr);
      return cv32_instr;
    end

    instr = riscv_instr::get_rand_instr (
      .exclude_instr    ( disallowed_instr ) ,
      .exclude_category ( exclude_category ) ,
      .include_group    ( {RV32X}          )
    );

    $cast(cv32_instr,instr);
    return cv32_instr;

  endfunction

  static function cv32e40p_instr get_cv32e40p_rand_instr(cv32e40p_instr instr_h = null,
                                             riscv_instr_name_t include_instr[$] = {},
                                             riscv_instr_name_t exclude_instr[$] = {},
                                             riscv_instr_category_t include_category[$] = {},
                                             riscv_instr_category_t exclude_category[$] = {},
                                             riscv_instr_group_t include_group[$] = {},
                                             riscv_instr_group_t exclude_group[$] = {});
     int unsigned idx;
     riscv_instr_name_t name;
     riscv_instr_name_t allowed_instr[$];
     riscv_instr_name_t disallowed_instr[$];
     riscv_instr_category_t allowed_categories[$];
     foreach (include_category[i]) begin
       allowed_instr = {allowed_instr, instr_category[include_category[i]]};
     end
     foreach (exclude_category[i]) begin
       if (instr_category.exists(exclude_category[i])) begin
         disallowed_instr = {disallowed_instr, instr_category[exclude_category[i]]};
       end
     end
     foreach (include_group[i]) begin
       allowed_instr = {allowed_instr, instr_group[include_group[i]]};
     end
     foreach (exclude_group[i]) begin
       if (instr_group.exists(exclude_group[i])) begin
         disallowed_instr = {disallowed_instr, instr_group[exclude_group[i]]};
       end
     end
     disallowed_instr = {disallowed_instr, exclude_instr};
     if (disallowed_instr.size() == 0) begin
       if (include_instr.size() > 0) begin
         idx = $urandom_range(0, include_instr.size()-1);
         name = include_instr[idx];
       end else if (allowed_instr.size() > 0) begin
         idx = $urandom_range(0, allowed_instr.size()-1);
         name = allowed_instr[idx];
       end else begin
         idx = $urandom_range(0, instr_names.size()-1);
         name = instr_names[idx];
       end
     end else begin
       if (!std::randomize(name) with {
          name inside {instr_names};
          if (include_instr.size() > 0) {
            name inside {include_instr};
          }
          if (allowed_instr.size() > 0) {
            name inside {allowed_instr};
          }
          if (disallowed_instr.size() > 0) {
            !(name inside {disallowed_instr});
          }
       }) begin
         `uvm_fatal("cv32e40p_instr", "Cannot generate random instruction")
       end
     end
     // Shallow copy for all relevant fields, avoid using create() to improve performance
     instr_h = new cv32e40p_instr_template[name];
     return instr_h;
  endfunction : get_cv32e40p_rand_instr

  static function riscv_instr get_load_store_instr(riscv_instr_name_t load_store_instr[$] = {});
    riscv_instr instr_h;
     int unsigned idx;
     int unsigned i;
     riscv_instr_name_t name;
     if (load_store_instr.size() == 0) begin
       load_store_instr = {instr_category[POST_INC_LOAD], instr_category[POST_INC_STORE]};
     end
     // Filter out unsupported load/store instruction
     if (unsupported_instr.size() > 0) begin
       while (i < load_store_instr.size()) begin
         if (load_store_instr[i] inside {unsupported_instr}) begin
           load_store_instr.delete(i);
         end else begin
           i++;
         end
       end
     end
     if (load_store_instr.size() == 0) begin
       $error("Cannot find available load/store instruction");
       $fatal(1);
     end
     idx = $urandom_range(0, load_store_instr.size()-1);
     name = load_store_instr[idx];
    //  $display("instr name is : %s", name);
     // Shallow copy for all relevant fields, avoid using create() to improve performance
     instr_h = new instr_template[name];
     return instr_h;
  endfunction : get_load_store_instr

  static function cv32e40p_instr get_cv32e40p_instr(riscv_instr_name_t name);
     riscv_instr instr_h;
     cv32e40p_instr cv32_instr;

     cv32_instr = cv32e40p_instr::type_id::create();

     if (!instr_template.exists(name)) begin
       `uvm_fatal("cv32e40p_instr", $sformatf("Cannot get instr %0s", name.name()))
     end
     // Shallow copy for all relevant fields, avoid using create() to improve performance
     instr_h = new instr_template[name];

     $cast(cv32_instr,instr_h);
     return cv32_instr;

     //return instr_h;
  endfunction : get_cv32e40p_instr

  // Disable the rand mode for unused operands to randomization performance
  virtual function void set_rand_mode();
    // post inc load and store encoding format is determined later, so all field should be randomized
    if (category inside {POST_INC_LOAD, POST_INC_STORE}) return;

    case (format) inside
      R_FORMAT : has_imm = 1'b0;
      I_FORMAT : has_rs2 = 1'b0;
      S_FORMAT, B_FORMAT : has_rd = 1'b0;
      U_FORMAT, J_FORMAT : begin
        has_rs1 = 1'b0;
        has_rs2 = 1'b0;
      end
    endcase

    // special overrides for xcorev

    // for ALU, there exists variations for R and S types
    if (category == ALU) begin
      if (instr_name inside {CV_CLIP, CV_CLIPU}) has_imm = 1'b1;
      if (format == S_FORMAT) has_rd = 1'b1;
    end

    if (category == CSR) begin
      has_rs2 = 1'b0;
      if (format == I_FORMAT) begin
        has_rs1 = 1'b0;
      end
    end
  endfunction

  function void pre_randomize();
    // determine post incr load store format and type
    if (category inside {POST_INC_LOAD, POST_INC_STORE}) begin
      std::randomize(is_r_format);
      if (is_r_format == 1) begin
        std::randomize(is_post_incr);
        this.format = R_FORMAT;
        has_imm = 0;
      end else begin
        is_post_incr = 1;
      end
    end

    if (category inside {HWLOOP}) std::randomize(hw_loop_label);

    rs1.rand_mode(has_rs1);
    rs2.rand_mode(has_rs2);
    rd.rand_mode(has_rd);
    imm.rand_mode(has_imm);
    if (category != CSR) begin
      csr.rand_mode(0);
    end
  endfunction

  virtual function void set_imm_len();
    if(format inside {U_FORMAT, J_FORMAT}) begin
      imm_len = 20;
    end else if(format inside {I_FORMAT, S_FORMAT, B_FORMAT}) begin
      if (category == BRANCH_IMM) begin
        imm_len = 17;
      end else if (category == BITMANIP) begin
        imm_len = 10;
      end else if (category == SIMD) begin
        imm_len = 6;
      end else if (category == HWLOOP) begin
        imm_len = (instr_name == CV_SETUPI) ? 17 : 12;
      end else if(imm_type == UIMM) begin
          imm_len = 5;
      end else begin
        imm_len = 12;
      end
    end

    if (category == ALU) imm_len = 5;

    imm_mask = imm_mask << imm_len;
  endfunction

  virtual function void extend_imm();
    bit sign;
    imm = imm << (32 - imm_len);
    sign = imm[31];
    imm = imm >> (32 - imm_len);
    // Signed extension
    if (sign && !((format == U_FORMAT) || (imm_type inside {UIMM, NZUIMM}))) begin
      imm = imm_mask | imm;
    end
  endfunction : extend_imm

  function void post_randomize();
    if (has_imm) begin
      extend_imm();
      update_imm_str();
    end
  endfunction : post_randomize

  // Convert the instruction to assembly code
  virtual function string convert2asm(string prefix = "");
    string asm_str;
    string asm_str_final;

    if (group != RV32X) begin
      super.convert2asm(prefix);
    end
    else begin
      asm_str = format_string(get_instr_name(),MAX_PULP_INSTR_STR_LEN);
      if(category != SYSTEM) begin
        case(format)
          I_FORMAT: begin // instr rd,rs1,imm more or less
            if(category == POST_INC_LOAD)
                asm_str_final = $sformatf("%0s %0s, (%0s), %0s", asm_str, rd.name(), rs1.name(), get_imm());
            else if (category == EVENT_LOAD)
              asm_str_final = $sformatf("%0s %0s, %0s(%0s)", asm_str, rd.name(), get_imm(), rs1.name());
            else if (category == BITMANIP)
              asm_str_final = $sformatf("%0s %0s, %0s, %0s", asm_str, rd.name(), rs1.name(), get_imm());
            else if (category == HWLOOP) begin
              if (instr_name inside {CV_COUNT, CV_START, CV_END} )
                asm_str_final = $sformatf("%0s %0b, %0s", asm_str, hw_loop_label, rs1.name());
              else if (instr_name inside {CV_SETUP} )
                asm_str_final = $sformatf("%0s %0b, %0s, %0s", asm_str, hw_loop_label, rs1.name(), get_imm());
              else
                asm_str_final = $sformatf("%0s %0b, %0s", asm_str, hw_loop_label, get_imm());
            end else
              asm_str_final = $sformatf("%0s %0s, %0s, %0s", asm_str, rd.name(), rs1.name(), get_imm());
          end
          R_FORMAT: begin
            if (category == POST_INC_LOAD) begin
              if(is_post_incr)
                asm_str_final = $sformatf("%0s %0s, (%0s), %0s", asm_str, rd.name(), rs1.name(), rs2.name());
              else
                asm_str_final = $sformatf("%0s %0s, %0s(%0s)", asm_str, rd.name(), rs2.name(), rs1.name());
            end

            else if (category == POST_INC_STORE) begin
              // rd is used as offset (rs3 in mnemonic, no use to add another register in the sv class just for this)
              if(is_post_incr)
                asm_str_final = $sformatf("%0s %0s, (%0s), %0s", asm_str, rs2.name(), rs1.name(), rd.name());
              else
                asm_str_final = $sformatf("%0s %0s, %0s(%0s)", asm_str, rs2.name(), rd.name(), rs1.name());
            end

            else if (category == BITMANIP && instr_name inside {CV_FF1, CV_FL1, CV_CLB, CV_CNT})
              asm_str_final = $sformatf("%0s %0s, %0s", asm_str, rd.name(), rs1.name());

            else if (category == ALU) begin
              if (instr_name inside {CV_ABS, CV_EXTHS, CV_EXTHZ, CV_EXTBS, CV_EXTBZ})
                asm_str_final = $sformatf("%0s %0s, %0s", asm_str, rd.name(), rs1.name());
              else if (instr_name inside {CV_CLIP, CV_CLIPU})
                asm_str_final = $sformatf("%0s %0s, %0s, %0s", asm_str, rd.name(), rs1.name(), get_imm());
              else asm_str_final = $sformatf("%0s %0s, %0s, %0s", asm_str, rd.name(), rs1.name(), rs2.name());
            end

            else if (instr_name inside {CV_ABS_H, CV_ABS_B, CV_CPLXCONJ})
                asm_str_final = $sformatf("%0s %0s, %0s", asm_str, rd.name(), rs1.name());

            else
              asm_str_final = $sformatf("%0s %0s, %0s, %0s", asm_str, rd.name(), rs1.name(), rs2.name());
          end
          S_FORMAT: begin // instr rs1,rs2,imm
            if(category == POST_INC_STORE)
              asm_str_final = $sformatf("%0s %0s, (%0s), %0s", asm_str, rs2.name(), rs1.name(), get_imm());
            else if (category inside {ALU, MAC} )
              asm_str_final = $sformatf("%0s %0s, %0s, %0s, %0s", asm_str, rd.name(), rs1.name(), rs2.name(), get_imm());
            else
              asm_str_final = super.convert2asm(prefix);
          end
          B_FORMAT: begin
            if (category == BRANCH_IMM) begin
              asm_str_final = $sformatf("%0s %0s, %0s", asm_str, rs1.name(), get_imm() );
            end else begin
              asm_str_final = $sformatf("%0s %0s, %0s, %0s", asm_str, rs1.name(), rs2.name(), get_imm());
            end
          end

          default: `uvm_fatal(`gfn, $sformatf("Unsupported format %0s [%0s]",
                                              format.name(), instr_name.name()))
        endcase
      end else begin
        super.convert2asm(prefix);
      end
    end

    if (comment == "") begin
      return asm_str_final.tolower();
    end else begin
      return {asm_str_final.tolower(), "    # ", comment};
    end

  endfunction

  function bit [6:0] get_opcode();
    case (instr_name) inside
      // LOAD n STORE + ELW
      CV_LB, CV_LH, CV_LW, CV_ELW, CV_LBU, CV_LHU      : get_opcode = (format == I_FORMAT) ? 7'b0001011 : 7'b0101011;
      CV_SB, CV_SH, CV_SW                              : get_opcode = 7'b0101011 ;
      // BRANCH IMM
      CV_BEQIMM, CV_BNEIMM                             : get_opcode = 7'b0001011;
      // HWLOOP
      CV_START, CV_STARTI, CV_END, CV_ENDI, CV_COUNT,
      CV_COUNTI, CV_SETUP, CV_SETUPI                   : get_opcode = 7'b0101011;
      // BIT MANIP
      CV_EXTRACTR, CV_EXTRACTUR, CV_INSERTR, CV_BCLRR,
      CV_BSETR, CV_ROR, CV_FF1, CV_FL1, CV_CLB, CV_CNT : get_opcode = 7'b0101011;
      CV_EXTRACT, CV_EXTRACTU, CV_INSERT, CV_BCLR,
      CV_BSET, CV_BITREV                               : get_opcode = 7'b1011011;
      // General ALU
      CV_ABS, CV_SLE, CV_SLEU, CV_MIN, CV_MINU,
      CV_MAX, CV_MAXU, CV_EXTHS, CV_EXTHZ, CV_EXTBS,
      CV_EXTBZ, CV_CLIP, CV_CLIPU, CV_CLIPR, CV_CLIPUR,
      CV_ADDNR, CV_ADDUNR, CV_ADDRNR, CV_ADDURNR,
      CV_SUBNR, CV_SUBUNR, CV_SUBRNR, CV_SUBURNR       : get_opcode = 7'b0101011;
      CV_ADDN, CV_ADDUN, CV_ADDRN, CV_ADDURN, CV_SUBN,
      CV_SUBUN, CV_SUBRN, CV_SUBURN                    : get_opcode = 7'b1011011;
      // MAC
      CV_MAC, CV_MSU                                   : get_opcode = 7'b0101011;
      CV_MULSN, CV_MULHHSN, CV_MULSRN, CV_MULHHSRN,
      CV_MULUN, CV_MULHHUN, CV_MULURN, CV_MULHHURN,
      CV_MACSN, CV_MACHHSN, CV_MACSRN, CV_MACHHSRN,
      CV_MACUN, CV_MACHHUN, CV_MACURN, CV_MACHHURN     : get_opcode = 7'b1011011;
      // SIMD
      CV_ADD_H, CV_ADD_B,
      CV_ADD_SC_H, CV_ADD_SC_B,
      CV_ADD_SCI_H, CV_ADD_SCI_B,
      CV_SUB_H, CV_SUB_B,
      CV_SUB_SC_H, CV_SUB_SC_B,
      CV_SUB_SCI_H, CV_SUB_SCI_B,
      CV_AVG_H, CV_AVG_B,
      CV_AVG_SC_H, CV_AVG_SC_B,
      CV_AVG_SCI_H, CV_AVG_SCI_B,
      CV_AVGU_H, CV_AVGU_B,
      CV_AVGU_SC_H, CV_AVGU_SC_B,
      CV_AVGU_SCI_H, CV_AVGU_SCI_B,
      CV_MIN_H, CV_MIN_B,
      CV_MIN_SC_H, CV_MIN_SC_B,
      CV_MIN_SCI_H, CV_MIN_SCI_B,
      CV_MINU_H, CV_MINU_B,
      CV_MINU_SC_H, CV_MINU_SC_B,
      CV_MINU_SCI_H, CV_MINU_SCI_B,
      CV_MAX_H, CV_MAX_B,
      CV_MAX_SC_H, CV_MAX_SC_B,
      CV_MAX_SCI_H, CV_MAX_SCI_B,
      CV_MAXU_H, CV_MAXU_B,
      CV_MAXU_SC_H, CV_MAXU_SC_B,
      CV_MAXU_SCI_H, CV_MAXU_SCI_B,
      CV_SRL_H, CV_SRL_B,
      CV_SRL_SC_H, CV_SRL_SC_B,
      CV_SRL_SCI_H, CV_SRL_SCI_B,
      CV_SRA_H, CV_SRA_B,
      CV_SRA_SC_H, CV_SRA_SC_B,
      CV_SRA_SCI_H, CV_SRA_SCI_B,
      CV_SLL_H, CV_SLL_B,
      CV_SLL_SC_H, CV_SLL_SC_B,
      CV_SLL_SCI_H, CV_SLL_SCI_B,
      CV_OR_H, CV_OR_B,
      CV_OR_SC_H, CV_OR_SC_B,
      CV_OR_SCI_H, CV_OR_SCI_B,
      CV_XOR_H, CV_XOR_B,
      CV_XOR_SC_H, CV_XOR_SC_B,
      CV_XOR_SCI_H, CV_XOR_SCI_B,
      CV_AND_H, CV_AND_B,
      CV_AND_SC_H, CV_AND_SC_B,
      CV_AND_SCI_H, CV_AND_SCI_B,
      CV_ABS_H, CV_ABS_B,
      CV_DOTUP_H, CV_DOTUP_B,
      CV_DOTUP_SC_H, CV_DOTUP_SC_B,
      CV_DOTUP_SCI_H, CV_DOTUP_SCI_B,
      CV_DOTUSP_H, CV_DOTUSP_B,
      CV_DOTUSP_SC_H, CV_DOTUSP_SC_B,
      CV_DOTUSP_SCI_H, CV_DOTUSP_SCI_B,
      CV_DOTSP_H, CV_DOTSP_B,
      CV_DOTSP_SC_H, CV_DOTSP_SC_B,
      CV_DOTSP_SCI_H, CV_DOTSP_SCI_B,
      CV_SDOTUP_H, CV_SDOTUP_B,
      CV_SDOTUP_SC_H, CV_SDOTUP_SC_B,
      CV_SDOTUP_SCI_H, CV_SDOTUP_SCI_B,
      CV_SDOTUSP_H, CV_SDOTUSP_B,
      CV_SDOTUSP_SC_H, CV_SDOTUSP_SC_B,
      CV_SDOTUSP_SCI_H, CV_SDOTUSP_SCI_B,
      CV_SDOTSP_H, CV_SDOTSP_B,
      CV_SDOTSP_SC_H, CV_SDOTSP_SC_B,
      CV_SDOTSP_SCI_H, CV_SDOTSP_SCI_B,
      CV_EXTRACT_H, CV_EXTRACT_B,
      CV_EXTRACTU_H, CV_EXTRACTU_B,
      CV_INSERT_H, CV_INSERT_B,
      CV_SHUFFLE_H, CV_SHUFFLE_B,
      CV_SHUFFLE_SCI_H,
      CV_SHUFFLEI0_SCI_B, CV_SHUFFLEI1_SCI_B,
      CV_SHUFFLEI2_SCI_B, CV_SHUFFLEI3_SCI_B,
      CV_SHUFFLE2_H, CV_SHUFFLE2_B,
      CV_PACK, CV_PACK_H, CV_PACKHI_B, CV_PACKLO_B,
      CV_CMPEQ_H, CV_CMPEQ_B,
      CV_CMPEQ_SC_H, CV_CMPEQ_SC_B,
      CV_CMPEQ_SCI_H, CV_CMPEQ_SCI_B,
      CV_CMPNE_H, CV_CMPNE_B,
      CV_CMPNE_SC_H, CV_CMPNE_SC_B,
      CV_CMPNE_SCI_H, CV_CMPNE_SCI_B,
      CV_CMPGT_H, CV_CMPGT_B,
      CV_CMPGT_SC_H, CV_CMPGT_SC_B,
      CV_CMPGT_SCI_H, CV_CMPGT_SCI_B,
      CV_CMPGE_H, CV_CMPGE_B,
      CV_CMPGE_SC_H, CV_CMPGE_SC_B,
      CV_CMPGE_SCI_H, CV_CMPGE_SCI_B,
      CV_CMPLT_H, CV_CMPLT_B,
      CV_CMPLT_SC_H, CV_CMPLT_SC_B,
      CV_CMPLT_SCI_H, CV_CMPLT_SCI_B,
      CV_CMPLE_H, CV_CMPLE_B,
      CV_CMPLE_SC_H, CV_CMPLE_SC_B,
      CV_CMPLE_SCI_H, CV_CMPLE_SCI_B,
      CV_CMPGTU_H, CV_CMPGTU_B,
      CV_CMPGTU_SC_H, CV_CMPGTU_SC_B,
      CV_CMPGTU_SCI_H, CV_CMPGTU_SCI_B,
      CV_CMPGEU_H, CV_CMPGEU_B,
      CV_CMPGEU_SC_H, CV_CMPGEU_SC_B,
      CV_CMPGEU_SCI_H, CV_CMPGEU_SCI_B,
      CV_CMPLTU_H, CV_CMPLTU_B,
      CV_CMPLTU_SC_H, CV_CMPLTU_SC_B,
      CV_CMPLTU_SCI_H, CV_CMPLTU_SCI_B,
      CV_CMPLEU_H, CV_CMPLEU_B,
      CV_CMPLEU_SC_H, CV_CMPLEU_SC_B,
      CV_CMPLEU_SCI_H, CV_CMPLEU_SCI_B,
      CV_CPLXMUL_R, CV_CPLXMUL_I,
      CV_CPLXMUL_R_DIV2, CV_CPLXMUL_R_DIV4, CV_CPLXMUL_R_DIV8,
      CV_CPLXMUL_I_DIV2, CV_CPLXMUL_I_DIV4, CV_CPLXMUL_I_DIV8,
      CV_CPLXCONJ, CV_SUBROTMJ,
      CV_SUBROTMJ_DIV2, CV_SUBROTMJ_DIV4, CV_SUBROTMJ_DIV8,
      CV_ADD_DIV2, CV_ADD_DIV4, CV_ADD_DIV8,
      CV_SUB_DIV2, CV_SUB_DIV4, CV_SUB_DIV8 : get_opcode = 7'b1111011;
      default : super.get_opcode();
    endcase
  endfunction

  function bit [2:0] func3_simd();
    string asm_str;
    string sci_str, sc_str, hb_str;
    asm_str = get_instr_name();
    sci_str = asm_str.substr(asm_str.len()-5, asm_str.len()-3);
    sc_str  = asm_str.substr(asm_str.len()-4, asm_str.len()-3);
    hb_str  = asm_str.substr(asm_str.len()-1, asm_str.len()-1);

    if (sci_str != "sci" && sc_str != "sc") return (hb_str == "h") ? 3'b000 : 3'b001;
    if (sci_str == "sci") return (hb_str == "h") ? 3'b110 : 3'b111;
    return (hb_str == "h") ? 3'b100 : 3'b101;
  endfunction

  virtual function bit [2:0] get_func3();
    if (category == SIMD ) return func3_simd();
    case (instr_name) inside
      CV_LB  : get_func3 = (format != R_FORMAT) ? 3'b000 : 3'b011;
      CV_SB  : get_func3 = (format != R_FORMAT) ? 3'b000 : 3'b011;
      CV_LH  : get_func3 = (format != R_FORMAT) ? 3'b001 : 3'b011;
      CV_SH  : get_func3 = (format != R_FORMAT) ? 3'b001 : 3'b011;
      CV_LW  : get_func3 = (format != R_FORMAT) ? 3'b010 : 3'b011;
      CV_SW  : get_func3 = (format != R_FORMAT) ? 3'b010 : 3'b011;
      CV_ELW : get_func3 = (format != R_FORMAT) ? 3'b011 : 3'b011;
      CV_LBU : get_func3 = (format != R_FORMAT) ? 3'b100 : 3'b011;
      CV_LHU : get_func3 = (format != R_FORMAT) ? 3'b101 : 3'b011;
      // BRANCH IMM
      CV_BEQIMM : get_func3 = 3'b110;
      CV_BNEIMM : get_func3 = 3'b111;
      // HWLOOP
      CV_START, CV_STARTI, CV_END, CV_ENDI, CV_COUNT,
      CV_COUNTI, CV_SETUP, CV_SETUPI                   : get_func3 = 3'b100;
      // BIT MANIP
      CV_EXTRACTR, CV_EXTRACTUR, CV_INSERTR, CV_BCLRR,
      CV_BSETR, CV_ROR, CV_FF1, CV_FL1, CV_CLB, CV_CNT : get_func3 = 3'b011;
      CV_EXTRACT, CV_EXTRACTU, CV_INSERT               : get_func3 = 3'b000;
      CV_BCLR, CV_BSET, CV_BITREV                      : get_func3 = 3'b001;
      // General ALU
      CV_ABS, CV_SLE, CV_SLEU, CV_MIN, CV_MINU,
      CV_MAX, CV_MAXU, CV_EXTHS, CV_EXTHZ, CV_EXTBS,
      CV_EXTBZ, CV_CLIP, CV_CLIPU, CV_CLIPR, CV_CLIPUR,
      CV_ADDNR, CV_ADDUNR, CV_ADDRNR, CV_ADDURNR,
      CV_SUBNR, CV_SUBUNR, CV_SUBRNR, CV_SUBURNR,
      CV_SUBN, CV_SUBUN, CV_SUBRN, CV_SUBURN           : get_func3 = 3'b011;
      CV_ADDN, CV_ADDUN, CV_ADDRN, CV_ADDURN           : get_func3 = 3'b010;
      // MAC
      CV_MAC, CV_MSU                                   : get_func3 = 3'b011;
      CV_MULSN, CV_MULHHSN, CV_MULSRN, CV_MULHHSRN     : get_func3 = 3'b100;
      CV_MULUN, CV_MULHHUN, CV_MULURN, CV_MULHHURN     : get_func3 = 3'b101;
      CV_MACSN, CV_MACHHSN, CV_MACSRN, CV_MACHHSRN     : get_func3 = 3'b110;
      CV_MACUN, CV_MACHHUN, CV_MACURN, CV_MACHHURN     : get_func3 = 3'b111;
      default : super.get_func3();
    endcase
  endfunction


  virtual function bit [6:0] get_func7();
    case (instr_name) inside
      CV_LB  : get_func7 = (is_post_incr == 1) ? 7'b000_0000 : 7'b000_0100;
      CV_LH  : get_func7 = (is_post_incr == 1) ? 7'b000_0001 : 7'b000_0101;
      CV_LW  : get_func7 = (is_post_incr == 1) ? 7'b000_0010 : 7'b000_0110;
      CV_LBU : get_func7 = (is_post_incr == 1) ? 7'b000_1000 : 7'b000_1100;
      CV_LHU : get_func7 = (is_post_incr == 1) ? 7'b000_1001 : 7'b000_1101;
      CV_SB  : get_func7 = (is_post_incr == 1) ? 7'b001_0000 : 7'b001_0100;
      CV_SH  : get_func7 = (is_post_incr == 1) ? 7'b001_0001 : 7'b001_0101;
      CV_SW  : get_func7 = (is_post_incr == 1) ? 7'b001_0010 : 7'b001_0110;
      default : super.get_func7();
    endcase
  endfunction

  // Convert the instruction to assembly code
  virtual function string convert2bin(string prefix = "");
    string binary;
     `uvm_warning("COREV-DV", "convert2bin has only been partially implemented for XPULP Instructions")
    case(format)
      I_FORMAT: begin
        if(category == LOAD && is_post_incr == 1)
          binary = $sformatf("%8h", {imm[11:0], rs1, get_func3(), rd, get_opcode()});
        else
          binary = super.convert2bin(prefix);
      end
      R_FORMAT: begin
        if (category == LOAD)
          binary = $sformatf("%8h", {get_func7(), rs2, rs1, get_func3(), rd, get_opcode()});
        else if (category == STORE)
          // rd is used as offset (rs3 in mnemonic, no use to add another register in the sv class just for this)
          binary = $sformatf("%8h", {get_func7(), rs2, rs1, get_func3(), rd, get_opcode()});
        else
        binary = super.convert2bin(prefix);
      end
      S_FORMAT: begin
        if(category == STORE && is_post_incr == 1)
          binary = $sformatf("%8h", {imm[11:5], rs2, rs1, get_func3(), imm[4:0], get_opcode()});
        else
          binary = super.convert2bin(prefix);
      end
      default: binary = super.convert2bin(prefix);
    endcase
    return {prefix, binary};
  endfunction

  virtual function string get_instr_name();
    get_instr_name = instr_name.name();
    foreach(get_instr_name[i]) begin
      if (get_instr_name[i] == "_") begin
        get_instr_name[i] = ".";
      end
    end
    return get_instr_name;
  endfunction


  // Default return imm value directly, can be overriden to use labels and symbols
  // Example: %hi(symbol), %pc_rel(label) ...
  virtual function string get_imm();
    return imm_str;
  endfunction

  virtual function void clear_unused_label();
    if(has_label && !is_branch_target && is_local_numeric_label) begin
      has_label = 1'b0;
    end
  endfunction

  virtual function void do_copy(uvm_object rhs);
    cv32e40p_instr rhs_;
    super.copy(rhs);
    assert($cast(rhs_, rhs));
    this.category = rhs_.category;
    this.is_post_incr      = rhs_.is_post_incr;
    this.is_r_format       = rhs_.is_r_format;
  endfunction : do_copy

  virtual function void update_imm_str();
    if (category == BRANCH_IMM) begin
      // for branch imm, immediate is split in two parts
      imm_str = $sformatf("%0d, %0d", $signed(imm[16:12]), $signed(imm[11:0]));
    end else if (category == BITMANIP) begin
      if (instr_name == CV_BITREV)
        imm_str = $sformatf("%0d, %0d", $unsigned({3'b000, imm[6:5]}), $unsigned(imm[4:0]));
      else
        imm_str = $sformatf("%0d, %0d", $unsigned(imm[9:5]), $unsigned(imm[4:0]));
    end else if (category == HWLOOP) begin
      if (instr_name == CV_SETUPI) begin
        imm_str = $sformatf("%0d, %0d", $unsigned(imm[11:0]), $unsigned(imm[16:12]));
      end else begin
        imm_str = $sformatf("%0d", $unsigned(imm[11:0]));
      end
    end else if (category == SIMD) begin
      if (imm_type == UIMM) begin
        imm_str = $sformatf("%0d", $unsigned(imm[5:0]));
      end else begin
        imm_str = $sformatf("%0d", $signed(imm[5:0]));
      end
    end else
    super.update_imm_str();
  endfunction

  // `include "isa/riscv_instr_cov.svh"

endclass
