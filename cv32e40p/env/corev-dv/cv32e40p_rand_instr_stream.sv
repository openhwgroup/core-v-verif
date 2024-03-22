/*
 * Copyright 2018 Google LLC
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
// Extended class from riscv_rand_instr_stream to override insert_instr_stream.
// Prevent instructions from multiple streams from overlapping each others and 
// to ensure the instructions order in one stream is preserved.
class cv32e40p_rand_instr_stream extends riscv_rand_instr_stream;

  // below properties are for insert_instr_stream function
  protected int         idx_start[$];            
  protected int         idx_end[$];            
  protected int         idx_min = 0;            
  cv32e40p_instr_gen_config cv32e40p_cfg;
  rand int unsigned     default_avail_reg;

  constraint def_avail_reg_c {
    if ((cfg.enable_fp_in_x_regs == 1) && (RV32ZFINX inside {riscv_instr_pkg::supported_isa})) {
      default_avail_reg >= 8;
      default_avail_reg <= (22 - cv32e40p_cfg.num_zfinx_reserved_reg);
    } else {
      default_avail_reg >= 8;
      default_avail_reg <= 22;
    }
  }

  `uvm_object_utils(cv32e40p_rand_instr_stream)
  //`uvm_object_new
  function new(string name = "");
    super.new(name);
    if(!uvm_config_db#(cv32e40p_instr_gen_config)::get(null,get_full_name(),"cv32e40p_instr_cfg", cv32e40p_cfg)) begin
      `uvm_fatal(get_full_name(), "Cannot get cv32e40p_instr_gen_config")
    end
  endfunction : new

  virtual function void insert_instr_stream(riscv_instr new_instr[], int idx = -1, bit replace = 1'b0);

    int current_instr_cnt = instr_list.size();
    int new_instr_cnt = new_instr.size(); // e.g from directed stream

    if (replace) begin
      `uvm_fatal(`gfn, $sformatf("Function implementation is not ready for replace==1"))
    end

    if(current_instr_cnt == 0) begin
      instr_list = new_instr;
      return;
    end
    if(idx == -1) begin

      bit idx_search_done = 0;
      int rand_cnt = 0;

      do begin 
        idx = $urandom_range(0, current_instr_cnt-1); 
      end while (instr_list[idx].atomic);
      while (!instr_list[idx].atomic && !idx_search_done) begin
        int idx_e = 0;
        idx_e = (idx + new_instr_cnt-1);

        if (idx_start.size() == 0) begin : SEARCH_IDX_FOR_NEW_INSTR
          idx_min = idx;
          idx_search_done = 1;
        end // SEARCH_IDX_FOR_NEW_INSTR
        else begin
          foreach (idx_start[i]) begin
            if (
              (idx          >= idx_start[i]   &&  idx           <= idx_end[i])  ||
              (idx_e        >= idx_start[i]   &&  idx_e         <= idx_end[i])  ||
              (idx_start[i] >= idx            &&  idx_start[i]  <= idx_e)       ||
              (idx_end[i]   >= idx            &&  idx_end[i]    <= idx_e)
            ) begin : DETECT_OVERLAP_IDX_FOR_NEW_INSTR
              break;
            end // DETECT_OVERLAP_IDX_FOR_NEW_INSTR
            else begin : NON_OVERLAP_IDX_FOR_NEW_INSTR
              if (i == (idx_start.size()-1)) begin
                idx_search_done = 1;
                break;
              end
            end // NON_OVERLAP_IDX_FOR_NEW_INSTR
          end // foreach
        end // SEARCH_IDX_FOR_NEW_INSTR

        if (idx_search_done) begin
          int idx_placement[$];
          if ((idx_start.size() == 0) || (idx_e < idx_min)) begin
            idx_min = idx;
            `uvm_info(`gfn, $sformatf("[DEBUG] - idx_min updated [%0d]", idx_min), UVM_DEBUG)
          end
          idx_start.push_back(idx);
          idx_end.push_back(idx_e);
          `uvm_info(`gfn, $sformatf("[DEBUG] - idx_start (before sort)       - %p", idx_start), UVM_DEBUG)
          `uvm_info(`gfn, $sformatf("[DEBUG] - idx_end   (before sort)       - %p", idx_end), UVM_DEBUG)
          idx_start.sort();
          idx_end.sort();
          `uvm_info(`gfn, $sformatf("[DEBUG] - idx_start (after sort)        - %p", idx_start), UVM_DEBUG)
          `uvm_info(`gfn, $sformatf("[DEBUG] - idx_end   (after sort)        - %p", idx_end), UVM_DEBUG)
          idx_placement = idx_start.find_first_index(x) with (x == idx);
          for (int i=idx_placement[0]+1; i<idx_start.size(); i++) begin
            idx_start[i] = idx_start[i]+new_instr_cnt;
            idx_end[i]   = idx_end[i]+new_instr_cnt;
            `uvm_info(`gfn, $sformatf("[DEBUG] - idx_start (update placement)  - %p", idx_start), UVM_DEBUG)
            `uvm_info(`gfn, $sformatf("[DEBUG] - idx_end   (update placement)  - %p", idx_end), UVM_DEBUG)
          end
        end // idx_search_done

        rand_cnt++;
        if (rand_cnt >= 200) begin
          int idx_placement[$];
          `uvm_info(`gfn, $sformatf("placement limit %0d reached. Place the stream at begining of instr_list", rand_cnt), UVM_NONE)
          idx = 0;
          idx_e = (idx + new_instr_cnt-1);
          idx_start.push_front(idx);
          idx_end.push_front(idx_e);
          idx_placement = idx_start.find_first_index(x) with (x == idx);
          for (int i=idx_placement[0]+1; i<idx_start.size(); i++) begin
            idx_start[i] = idx_start[i]+new_instr_cnt;
            idx_end[i]   = idx_end[i]+new_instr_cnt;
          end
          break;
        end // rand_cnt

        do begin 
          idx = $urandom_range(0, current_instr_cnt-1); 
        end while (instr_list[idx].atomic);

      end // while

      if (instr_list[idx].atomic) begin
        foreach (instr_list[i]) begin
          if (!instr_list[i].atomic) begin
            idx = i;
            break;
          end
        end
        if (instr_list[idx].atomic) begin
          `uvm_fatal(`gfn, $sformatf("Cannot inject the instruction"))
        end
      end // instr_list[idx].atomic

    end else if((idx > current_instr_cnt) || (idx < 0)) begin
      `uvm_error(`gfn, $sformatf("Cannot insert instr stream at idx %0d", idx))
    end // idx

    // When replace is 1, the original instruction at this index will be removed. The label of the
    // original instruction will be copied to the head of inserted instruction stream.
    if(replace) begin
      new_instr[0].label = instr_list[idx].label;
      new_instr[0].has_label = instr_list[idx].has_label;
      if (idx == 0) instr_list = {new_instr, instr_list[idx+1:current_instr_cnt-1]};
      else          instr_list = {instr_list[0:idx-1], new_instr, instr_list[idx+1:current_instr_cnt-1]};
    end else begin
      if (idx == 0) instr_list = {new_instr, instr_list[idx:current_instr_cnt-1]};
      else          instr_list = {instr_list[0:idx-1], new_instr, instr_list[idx:current_instr_cnt-1]};
    end

  endfunction

  // Override base class randomize_avail_regs function
  // Add randomization for number of registers to be randomized
  virtual function void randomize_avail_regs();
    std::randomize(default_avail_reg) with  {  if ((cfg.enable_fp_in_x_regs == 1) && (RV32ZFINX inside {riscv_instr_pkg::supported_isa})) {
                                                 default_avail_reg >= 8;
                                                 default_avail_reg <= (22 - cv32e40p_cfg.num_zfinx_reserved_reg);
                                               } else {
                                                 default_avail_reg >= 8;
                                                 default_avail_reg <= 22;
                                               }
                                            };

    avail_regs = new[default_avail_reg];
    if(avail_regs.size() > 0) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(avail_regs,
                                         unique{avail_regs};
                                         avail_regs[0] inside {[S0 : A5]};
                                         foreach(avail_regs[i]) {
                                           !(avail_regs[i] inside {cfg.reserved_regs, reserved_rd});
                                         },
                                         "Cannot randomize avail_regs")
    end
  endfunction


  //Function: cv32e40p_rand_instr_stream::gen_instr()
  //override the parent class gen_instr() inside cv32e40p_rand_instr_stream
  virtual function void gen_instr(bit no_branch = 1'b0, bit no_load_store = 1'b1,
                                  bit is_debug_program = 1'b0);
    setup_allowed_instr(no_branch, no_load_store);

    // Need to randomize avail_regs[] to ensure the randomize_gpr() call
    // actually randomize the registers for each instruction.
    // And this also ensures the randomization is done separately for each
    // program section.
    // This also ensures reserved_regs get removed from gpr randomization
    // for each instruction.
    randomize_avail_regs();

    `uvm_info("cv32e40p_rand_instr_stream", $sformatf("Randomized default_avail_reg = %d", default_avail_reg), UVM_DEBUG)
    foreach(avail_regs[i]) begin
        `uvm_info("cv32e40p_rand_instr_stream", $sformatf("Randomized avail_regs[%d] = %s", i, avail_regs[i]), UVM_DEBUG)
    end

    //Use this plusarg - include_xpulp_instr_in_debug_rom to include xpulp instr
    //In random debug_rom instructions. Added for v2 debug tests with xpulp.
    if (cv32e40p_cfg.xpulp_instr_in_debug_rom && is_debug_program && $test$plusargs("include_xpulp_instr_in_debug_rom")) begin
        `uvm_info("cv32e40p_rand_instr_stream", $sformatf("Including xpulp instr in debug_rom"), UVM_LOW)
        foreach(instr_list[i]) begin
          randcase
            1: randomize_debug_rom_instr(.instr(instr_list[i]), .is_in_debug(is_debug_program), .disable_dist());
            2: randomize_instr(instr_list[i], is_debug_program);
          endcase
          store_instr_gpr_handling(instr_list[i]);
        end
    end
    else begin
        foreach(instr_list[i])
          randomize_instr(instr_list[i], is_debug_program);
    end
    // Do not allow branch instruction as the last instruction because there's no
    // forward branch target
    while (instr_list[$].category == BRANCH) begin
      void'(instr_list.pop_back());
      if (instr_list.size() == 0) break;
    end
  endfunction

  //Function: randomize_debug_rom_instr()
  //Added for v2 debug tests to generate random instructions for debug_rom.
  //Need to create this function to handle xpulp specific randomization
  //which is not available in parent class func randomize_instr()
  function void randomize_debug_rom_instr(output riscv_instr instr,
                                input  bit is_in_debug = 1'b1,
                                input  bit disable_dist = 1'b0,
                                input  riscv_instr_group_t include_group[$] = {});
    riscv_instr_name_t exclude_instr[];
    if ((SP inside {reserved_rd, cfg.reserved_regs}) ||
        ((avail_regs.size() > 0) && !(SP inside {avail_regs}))) begin
      exclude_instr = {C_ADDI4SPN, C_ADDI16SP, C_LWSP, C_LDSP};
    end
    // Post-process the allowed_instr and exclude_instr lists to handle
    // adding ebreak instructions to the debug rom.
    if (is_in_debug) begin
      if (cfg.enable_ebreak_in_debug_rom) begin
        allowed_instr = {allowed_instr, EBREAK, C_EBREAK};
      end else begin
        exclude_instr = {exclude_instr, EBREAK, C_EBREAK};
      end
    end

    if(cfg.no_branch_jump) begin
      exclude_instr = {exclude_instr, CV_BEQIMM, CV_BNEIMM, BEQ, BNE, BLT, BGE, BLTU, BGEU, C_BEQZ, C_BNEZ, JALR, JAL, C_JR, C_JALR, C_J, C_JAL};
    end

    exclude_instr = {exclude_instr, CV_START, CV_STARTI, CV_END, CV_ENDI, CV_COUNT, CV_COUNTI, CV_SETUP, CV_SETUPI, CV_ELW, C_ADDI16SP, C_SWSP, C_FSWSP, URET, SRET, MRET, DRET, ECALL};
    instr = riscv_instr::get_rand_instr(.exclude_instr(exclude_instr));
    instr.m_cfg = cfg;
    randomize_gpr(instr);
  endfunction

  // Function to assign reserved reg for store instr from cfg to avoid random
  // reg operands for stores which may result in corruption of instr memory
  function void store_instr_gpr_handling(riscv_instr instr);
    if (instr.instr_name inside {SB, SH, SW, C_SW, C_FSW, FSW, CV_SB, CV_SH, CV_SW}) begin
      instr.rs1 = cv32e40p_cfg.str_rs1;
      instr.rd  = cv32e40p_cfg.str_rs3;
    end
  endfunction

endclass

