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

// cv32e40p specific stream classes extended from RISCV-DV stream classes

 class cv32e40p_base_instr_stream extends riscv_rand_instr_stream;

  rand bit [31:0]           temp_imm; // variable used for immediate value randomization
  cv32e40p_instr_gen_config cv32e40p_cfg;

  `uvm_object_utils(cv32e40p_base_instr_stream)
  int unsigned num_of_avail_regs;

  function new(string name = "");
    super.new(name);
  endfunction

  function void pre_randomize();
    `DV_CHECK_FATAL($cast(cv32e40p_cfg, cfg), "Could not cast cfg into cv32e40p_cfg")
    super.pre_randomize();
  endfunction

  virtual function void setup_allowed_instr(bit no_branch = 1'b0, bit no_load_store = 1'b1);
      allowed_instr = riscv_instr::basic_instr;
      if (no_branch == 0) begin
        allowed_instr = {allowed_instr, riscv_instr::instr_category[BRANCH],
                                        riscv_instr::instr_category[BRANCH_IMM]};
      end
      if (no_load_store == 0) begin
        allowed_instr = {allowed_instr, riscv_instr::instr_category[LOAD],
                                        riscv_instr::instr_category[STORE],
                                        riscv_instr::instr_category[POST_INC_LOAD],
                                        riscv_instr::instr_category[POST_INC_STORE]};
      end
      setup_instruction_dist(no_branch, no_load_store);
    endfunction

  function void setup_instruction_dist(bit no_branch = 1'b0, bit no_load_store = 1'b1);
  if (cfg.dist_control_mode) begin
      category_dist = cfg.category_dist;
      if (no_branch) begin
        category_dist[BRANCH] = 0;
        category_dist[BRANCH_IMM] = 0;
      end
      if (no_load_store) begin
        category_dist[LOAD] = 0;
        category_dist[STORE] = 0;
        category_dist[POST_INC_LOAD] = 0;
        category_dist[POST_INC_STORE] = 0;
      end
      `uvm_info(`gfn, $sformatf("setup_instruction_dist: %0d", category_dist.size()), UVM_LOW)
  end
  endfunction

  function void post_randomize();
    for (int i = 0; i < instr_list.size(); i++) begin
      instr_list[i].comment = {instr_list[i].comment, $sformatf(" Inserted %0s - idx[%0d]", get_name(), i)};
    end
    super.post_randomize();
  endfunction : post_randomize

  //Function: randomize_cv32e40p_gpr()
  //Similar to randomize_gpr() of parent class which is not a virtual method
  //Thus need to create a new function here for cv32e40p_instr instr type
  function void randomize_cv32e40p_gpr(cv32e40p_instr instr, riscv_reg_t avail_reg_list[]);
    instr.set_rand_mode();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      if ( (format != (CI_FORMAT || CB_FORMAT || CJ_FORMAT || CR_FORMAT || CA_FORMAT || CL_FORMAT || CS_FORMAT || CSS_FORMAT || CIW_FORMAT)) ) {
        if (avail_reg_list.size() > 0) {
          if (has_rs1) {
            rs1 inside {avail_reg_list};
          }
          if (has_rs2) {
            rs2 inside {avail_reg_list};
          }
          if (has_rd) {
            rd  inside {avail_reg_list};
          }
        }
        foreach (reserved_rd[i]) {
          if (has_rd) {
            rd != reserved_rd[i];
          }
          if (format == CB_FORMAT) {
            rs1 != reserved_rd[i];
          }
          if ((category == POST_INC_LOAD) || (category == POST_INC_STORE)) {
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
          if ((category == POST_INC_LOAD) || (category == POST_INC_STORE)) {
            rs1 != cfg.reserved_regs[i];
          }
        }
      }
      // TODO: Add constraint for CSR, floating point register
    )

    if (instr.instr_name inside {SB, SH, SW, C_SW, C_FSW, FSW, CV_SB, CV_SH, CV_SW}) begin
      instr.rs1 = cv32e40p_cfg.str_rs1;
      instr.rd  = cv32e40p_cfg.str_rs3;
    end

  endfunction

  //Function: randomize_cv32e40p_instr_imm()
  //Function to randomize immediates for cv32e40p_instr type.
  //It solves the issue where if same instruction is generated in a stream
  //multiple times, the immediate values were not re-randomized as they
  //were only randomized once during creation of instruction class
  function void randomize_cv32e40p_instr_imm(cv32e40p_instr instr);
    //std::randomize(temp_imm);
    if (instr.is_compressed) begin
      std::randomize(temp_imm) with  {
                                       if(instr.imm_type inside {NZIMM, NZUIMM}) {
                                         temp_imm[4:0] != 0;
                                         if (instr.instr_name == C_LUI) {
                                           temp_imm[31:5] == 0;
                                         }
                                         if (instr.instr_name == (C_SRAI || C_SRLI || C_SLLI || C_LUI)) {
                                           temp_imm[31:5] == 0;
                                         }
                                       }
                                       if (instr.instr_name == C_ADDI4SPN) {
                                         temp_imm[1:0] == 0;
                                       }
                                     };
      instr.imm = temp_imm;
    end
    else begin
      std::randomize(temp_imm) with  {
                                       if (instr.instr_name inside {SLLIW, SRLIW, SRAIW}) {
                                         temp_imm[11:5] == 0;
                                       }
                                       if (instr.instr_name inside {SLLI, SRLI, SRAI}) {
                                         if (XLEN == 32) {
                                           temp_imm[11:5] == 0;
                                         } else {
                                           temp_imm[11:6] == 0;
                                         }
                                       }
                                     };

      instr.imm = temp_imm;

      if (instr.has_imm) begin
        instr.extend_imm();
        instr.update_imm_str();
      end
    end
  endfunction

  //Function: randomize_riscv_instr_imm()
  //Function to randomize immediates for riscv_instr type.
  //It solves the issue where if same instruction is generated in a stream
  //multiple times, the immediate values were not re-randomized as they
  //were only randomized once during creation of instruction class
  function void randomize_riscv_instr_imm(riscv_instr instr);

    if (instr.is_compressed) begin
      std::randomize(temp_imm) with  {
                                       if(instr.imm_type inside {NZIMM, NZUIMM}) {
                                         temp_imm[4:0] != 0;
                                         if (instr.instr_name == C_LUI) {
                                           temp_imm[31:5] == 0;
                                         }
                                         if (instr.instr_name == (C_SRAI || C_SRLI || C_SLLI || C_LUI)) {
                                           temp_imm[31:5] == 0;
                                         }
                                       }
                                       if (instr.instr_name == C_ADDI4SPN) {
                                         temp_imm[1:0] == 0;
                                       }
                                     };
      instr.imm = temp_imm;
    end
    else begin
      std::randomize(temp_imm) with  {
                                       if (instr.instr_name inside {SLLIW, SRLIW, SRAIW}) {
                                         temp_imm[11:5] == 0;
                                       }
                                       if (instr.instr_name inside {SLLI, SRLI, SRAI}) {
                                         if (XLEN == 32) {
                                           temp_imm[11:5] == 0;
                                         } else {
                                           temp_imm[11:6] == 0;
                                         }
                                       }
                                     };
      instr.imm = temp_imm;
      instr.extend_imm();
      instr.update_imm_str();
    end
  endfunction

  //Function: randomize_zfinx_gpr()
  function void randomize_zfinx_gpr(riscv_fp_in_x_regs_instr instr, riscv_reg_t avail_reg_list[]);
    instr.set_rand_mode();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      if ( (format != (CI_FORMAT || CB_FORMAT || CJ_FORMAT || CR_FORMAT || CA_FORMAT || CL_FORMAT || CS_FORMAT || CSS_FORMAT || CIW_FORMAT)) ) {
        if (avail_reg_list.size() > 0) {
          if (has_rs1) {
            rs1 inside {avail_reg_list};
          }
          if (has_rs2) {
            rs2 inside {avail_reg_list};
          }
          if (has_rs3) {
            rs3 inside {avail_reg_list};
          }
          if (has_rd) {
            rd  inside {avail_reg_list};
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
      }
    )
  endfunction

  // Function to assign reserved reg for store instr from cfg to avoid random
  // reg operands for stores which may result in corruption of instr memory
  function void store_instr_gpr_handling(riscv_instr instr);
    if (instr.instr_name inside {SB, SH, SW, C_SW, C_FSW, FSW, CV_SB, CV_SH, CV_SW}) begin
      instr.rs1 = cv32e40p_cfg.str_rs1;
      instr.rd  = cv32e40p_cfg.str_rs3;
    end
  endfunction

endclass // cv32e40p_base_instr_stream
