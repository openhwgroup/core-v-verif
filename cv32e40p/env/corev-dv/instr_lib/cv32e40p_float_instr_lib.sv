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

class cv32e40p_float_zfinx_base_instr_stream extends cv32e40p_base_instr_stream;

  string _header;
  bit    is_zfinx; // only used as a shorthand for RV32ZFINX inside {riscv_instr_pkg::supported_isa}, and initialized in "new" method


  rand int unsigned num_of_avail_regs;
  rand int unsigned num_of_instr_per_stream;
  rand riscv_fpr_t  avail_fp_regs[];
  rand riscv_fpr_t  reserved_fd[];   

  rand riscv_instr_name_t     exclude_instr[];
  rand riscv_instr_category_t exclude_category[];
  rand riscv_instr_group_t    exclude_group[];

  `uvm_object_utils(cv32e40p_float_zfinx_base_instr_stream)

  constraint c_others {
    soft num_of_avail_regs == 10; // todo: currently set to 10 for testing
    num_of_instr_per_stream > 0;
    soft num_of_instr_per_stream inside {[1:20]};
  }

  constraint c_x_regs {
    soft avail_regs.size() == num_of_avail_regs;
    unique{avail_regs};
    avail_regs[0] inside {[S0:A5]};
    foreach(avail_regs[i]) {
      !(avail_regs[i] inside {cfg.reserved_regs, reserved_rd});
    }
  }

  constraint c_fp_regs {
    soft avail_fp_regs.size() == num_of_avail_regs;
    unique{avail_fp_regs};
    avail_fp_regs[0] inside {[FT0:FT7]};
  }

  function new (string name="");
    super.new(name);
    _header = this.type_name;
    if ( !(riscv_instr_pkg::RV32ZFINX inside {riscv_instr_pkg::supported_isa}) && ! (riscv_instr_pkg::RV32F inside {riscv_instr_pkg::supported_isa}) ) begin
      `uvm_error(_header, $sformatf("RV32ZFINX and RV32F are not defined in RV_DV_ISA - refer cv32e40p_supported_isa.svh"));
    end
    is_zfinx = riscv_instr_pkg::RV32ZFINX inside {riscv_instr_pkg::supported_isa};
  endfunction // new

  function void pre_randomize();
    super.pre_randomize();
  endfunction // pre_randomize

  function void post_randomize();
    riscv_instr                 instr;
    riscv_fp_in_x_regs_instr    instr_zfinx;
    riscv_floating_point_instr  instr_f;

    `uvm_info(_header, $sformatf("supported_isa[%p] with num_of_instr_per_stream[%0d]", supported_isa, num_of_instr_per_stream), UVM_DEBUG);
    for (int i = 0; i < num_of_instr_per_stream; i++) begin
      if (is_zfinx) begin
        instr = get_zfinx_instr();
        `uvm_info(_header, $sformatf("instr[%s] and avail_regs[%p]", instr.instr_name.name(), avail_regs), UVM_DEBUG);
        `DV_CHECK_FATAL($cast(instr_zfinx, instr), "Cast to instr_zfinx failed!");
        randomize_gpr_zfinx(instr_zfinx);
        instr_list.push_back(instr_zfinx);
      end
      else begin
        instr = get_float_instr();
        `uvm_info(_header, $sformatf("instr[%s] and avail_fp_regs[%p]", instr.instr_name.name(), avail_fp_regs), UVM_DEBUG);
        `DV_CHECK_FATAL($cast(instr_f, instr), "Cast to instr_f failed!");
        randomize_fpr(instr_f);
        instr_list.push_back(instr_f);
      end 
    end // num_of_instr_per_stream

    super.post_randomize();
  endfunction // post_randomize

  // randomize registers to be used in this instr
  function void randomize_gpr_zfinx(riscv_fp_in_x_regs_instr instr);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      if (local::avail_regs.size() > 0) {
        if (has_rs1) {
          rs1 inside {avail_regs};
        }
        if (has_rs2) {
          rs2 inside {avail_regs};
        }
        if (has_rs3) {
          rs3 inside {avail_regs};
        }
        if (has_rd) {
          rd  inside {avail_regs};
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
    )
  endfunction // randomize_gpr_zfinx

  function void randomize_fpr(riscv_floating_point_instr instr);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
        if (local::avail_fp_regs.size() >0) {
          if (has_fs1) {
            fs1 inside {avail_fp_regs};
          }
          if (has_fs2) {
            fs2 inside {avail_fp_regs};
          }
          if (has_fs3) {
            fs3 inside {avail_fp_regs};
          }
          if (has_fd) {
            fd inside {avail_fp_regs};
          }
        }
    )
  endfunction // randomize_fpr

  virtual function riscv_instr get_zfinx_instr();
      return riscv_instr::get_rand_instr(
        .include_group({RV32ZFINX})
      );
  endfunction // get_zfinx_instr

  virtual function riscv_instr get_float_instr();
    if (XLEN >= 64) begin
      return riscv_instr::get_rand_instr(
        .include_group({RV32F, RV64F})
      );
    end else begin
      return riscv_instr::get_rand_instr(
        .include_group({RV32F})
      );
    end
  endfunction // get_float_instr

endclass // cv32e40p_float_zfinx_base_instr_stream

