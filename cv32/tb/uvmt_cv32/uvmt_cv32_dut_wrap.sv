//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technologies
// 
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     https://solderpad.org/licenses/
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// 
///////////////////////////////////////////////////////////////////////////////
//
// Modified version of the wrapper for a RI5CY testbench, containing RI5CY,
// plus Memory and stdout virtual peripherals.
// Contributor: Robert Balas <balasr@student.ethz.ch>
// Copyright 2018 Robert Balas <balasr@student.ethz.ch>
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//


`ifndef __UVMT_CV32_DUT_WRAP_SV__
`define __UVMT_CV32_DUT_WRAP_SV__


/**
 * Module wrapper for CV32 RTL DUT.
 */
module uvmt_cv32_dut_wrap #(// DUT (riscv_core) parameters.
                            // https://github.com/openhwgroup/core-v-docs/blob/master/cores/cv32e40p/CV32E40P_and%20CV32E40_Features_Parameters.pdf
                            parameter PULP_XPULP          =  0,
                                      PULP_CLUSTER        =  0,
                                      FPU                 =  0,
                                      PULP_ZFINX          =  0,
                                      NUM_MHPMCOUNTERS    =  1,
                            // Remaining parameters are used by TB components only
                                      INSTR_ADDR_WIDTH    =  32,
                                      INSTR_RDATA_WIDTH   =  32,
                                      RAM_ADDR_WIDTH      =  20
                           )

                           (
                            uvma_clknrst_if              clknrst_if,
                            uvmt_cv32_vp_status_if       vp_status_if,
                            uvmt_cv32_core_cntrl_if      core_cntrl_if,
                            uvmt_cv32_core_status_if     core_status_if,
                            uvmt_cv32_core_interrupts_if core_interrupts_if
                           );

    import uvm_pkg::*; // needed for the UVM messaging service (`uvm_info(), etc.)

    // signals connecting core to memory
    logic                         instr_req;
    logic                         instr_gnt;
    logic                         instr_rvalid;
    logic [INSTR_ADDR_WIDTH-1 :0] instr_addr;
    logic [INSTR_RDATA_WIDTH-1:0] instr_rdata;

    logic                         data_req;
    logic                         data_gnt;
    logic                         data_rvalid;
    logic [31:0]                  data_addr;
    logic                         data_we;
    logic [3:0]                   data_be;
    logic [31:0]                  data_rdata;
    logic [31:0]                  data_wdata;

    logic [ 4:0]                  irq_id_in;

    logic [63:0]                  irq64;
    logic [31:0]                  irq32;
    logic                         irq_ack;
    logic [ 5:0]                  irq_id6;
    logic [ 4:0]                  irq_id5;

    logic                         debug_req;
   
    // Hold interrupts idle for now
    assign irq64 = {64{1'b0}};
    assign irq32 = {32{1'b0}};

    // Load the Instruction Memory 
    initial begin: load_instruction_memory
      string firmware;
      int    fd;
       int   fill_cnt;
       bit [7:0] rnd_byte;
      `uvm_info("DUT_WRAP", "waiting for load_instr_mem to be asserted.", UVM_DEBUG)
      wait(core_cntrl_if.load_instr_mem !== 1'bX);
      if(core_cntrl_if.load_instr_mem === 1'b1) begin
        `uvm_info("DUT_WRAP", "load_instr_mem asserted!", UVM_NONE)

        // Load the pre-compiled firmware
        if($value$plusargs("firmware=%s", firmware)) begin
          // First, check if it exists...
          fd = $fopen (firmware, "r");   
          if (fd)  `uvm_info ("DUT_WRAP", $sformatf("%s was opened successfully : (fd=%0d)", firmware, fd), UVM_DEBUG)
          else     `uvm_fatal("DUT_WRAP", $sformatf("%s was NOT opened successfully : (fd=%0d)", firmware, fd))
          $fclose(fd);
          // Now load it...
          `uvm_info("DUT_WRAP", $sformatf("loading firmware %0s", firmware), UVM_NONE)
          $readmemh(firmware, uvmt_cv32_tb.dut_wrap.ram_i.dp_ram_i.mem);
          `ifdef ISS
             // If using ISS for any location in RTL mem = X fill RTL and ISS memory with same random value
             fill_cnt = 0;
             for (int index=0; index < 2**RAM_ADDR_WIDTH; index++) begin
                if (uvmt_cv32_tb.dut_wrap.ram_i.dp_ram_i.mem[index] === 8'hXX) begin
                    fill_cnt++;
                   rnd_byte = $random();
                   uvmt_cv32_tb.dut_wrap.ram_i.dp_ram_i.mem[index]=rnd_byte;
                   uvmt_cv32_tb.iss_wrap.ram.mem[index/4][((((index%4)+1)*8)-1)-:8]=rnd_byte; // convert byte to 32-bit addressing
                end
             end
             `uvm_info("DUT_WRAP", $sformatf("Filled 0d%0d RTL and ISS memory bytes with random values", fill_cnt), UVM_HIGH)
          `endif
        end
        else begin
          `uvm_error("DUT_WRAP", "No firmware specified!")
        end
      end
      else begin
        `uvm_info("DUT_WRAP", "NO TEST PROGRAM", UVM_NONE)
      end
    end

    // --------------------------------------------
    // instantiate the core
    cv32e40p_core #(
                 .PULP_XPULP       (PULP_XPULP),
                 .PULP_CLUSTER     (PULP_CLUSTER),
                 .FPU              (FPU),
                 .PULP_ZFINX       (PULP_ZFINX),
                 .NUM_MHPMCOUNTERS (NUM_MHPMCOUNTERS)
                )
    riscv_core_i
        (
         .clk_i                  ( clknrst_if.clk                 ),
         .rst_ni                 ( clknrst_if.reset_n             ),

         .pulp_clock_en_i        ( core_cntrl_if.clock_en         ),
         .scan_cg_en_i           ( core_cntrl_if.scan_cg_en       ),

         .boot_addr_i            ( core_cntrl_if.boot_addr        ),
         .mtvec_addr_i           ( core_cntrl_if.mtvec_addr       ),
         .dm_halt_addr_i         ( core_cntrl_if.dm_halt_addr     ),
         .hart_id_i              ( core_cntrl_if.hart_id          ),
         .dm_exception_addr_i    (  32'h1A110C00                  ),


         .instr_req_o            ( instr_req                      ),
         .instr_gnt_i            ( instr_gnt                      ),
         .instr_rvalid_i         ( instr_rvalid                   ),
         .instr_addr_o           ( instr_addr                     ),
         .instr_rdata_i          ( instr_rdata                    ),

         .data_req_o             ( data_req                       ),
         .data_gnt_i             ( data_gnt                       ),
         .data_rvalid_i          ( data_rvalid                    ),
         .data_we_o              ( data_we                        ),
         .data_be_o              ( data_be                        ),
         .data_addr_o            ( data_addr                      ),
         .data_wdata_o           ( data_wdata                     ),
         .data_rdata_i           ( data_rdata                     ),

         .apu_master_req_o       (                                ),
         .apu_master_ready_o     (                                ),
         .apu_master_gnt_i       (                                ),
         .apu_master_operands_o  (                                ),
         .apu_master_op_o        (                                ),
         .apu_master_type_o      (                                ),
         .apu_master_flags_o     (                                ),
         .apu_master_valid_i     (                                ),
         .apu_master_result_i    (                                ),
         .apu_master_flags_i     (                                ),

         // TODO: interrupts significantly updated for CV32E40P
         //       Connect all interrupt signals to an SV interface
         //       and pass to ENV for an INTERRUPT AGENT to drive/monitor.
         .irq_i                  ( irq32                          ),
         .irq_ack_o              ( irq_ack                        ),
         .irq_id_o               ( irq_id5                        ),

         .debug_req_i            ( debug_req                      ),

         .fetch_enable_i         ( core_cntrl_if.fetch_en         ),
         .core_sleep_o           ( core_status_if.core_busy       )
        ); //riscv_core_i

    bind cv32e40p_core cv32e40p_tracer tracer_i(
      .clk_i              ( clknrst_if.clk                                    ), // always-running clock for tracing
      .rst_n              ( clknrst_if.reset_n                                ),

      .hart_id_i          ( core_cntrl_if.hart_id                             ),

      .pc                 ( riscv_core_i.id_stage_i.pc_id_i                   ),
      .instr              ( riscv_core_i.id_stage_i.instr                     ),
      .controller_state_i ( riscv_core_i.id_stage_i.controller_i.ctrl_fsm_cs  ),
      .compressed         ( riscv_core_i.id_stage_i.is_compressed_i           ),
      .id_valid           ( riscv_core_i.id_stage_i.id_valid_o                ),
      .is_decoding        ( riscv_core_i.id_stage_i.is_decoding_o             ),
      .is_illegal         ( riscv_core_i.id_stage_i.illegal_insn_dec          ),
      .rs1_value          ( riscv_core_i.id_stage_i.operand_a_fw_id           ),
      .rs2_value          ( riscv_core_i.id_stage_i.operand_b_fw_id           ),
      .rs3_value          ( riscv_core_i.id_stage_i.alu_operand_c             ),
      .rs2_value_vec      ( riscv_core_i.id_stage_i.alu_operand_b             ),

      .rs1_is_fp          ( riscv_core_i.id_stage_i.regfile_fp_a              ),
      .rs2_is_fp          ( riscv_core_i.id_stage_i.regfile_fp_b              ),
      .rs3_is_fp          ( riscv_core_i.id_stage_i.regfile_fp_c              ),
      .rd_is_fp           ( riscv_core_i.id_stage_i.regfile_fp_d              ),

      .ex_valid           ( riscv_core_i.ex_valid                             ),
      .ex_reg_addr        ( riscv_core_i.regfile_alu_waddr_fw                 ),
      .ex_reg_we          ( riscv_core_i.regfile_alu_we_fw                    ),
      .ex_reg_wdata       ( riscv_core_i.regfile_alu_wdata_fw                 ),

      .ex_data_addr       ( riscv_core_i.data_addr_o                          ),
      .ex_data_req        ( riscv_core_i.data_req_o                           ),
      .ex_data_gnt        ( riscv_core_i.data_gnt_i                           ),
      .ex_data_we         ( riscv_core_i.data_we_o                            ),
      .ex_data_wdata      ( riscv_core_i.data_wdata_o                         ),
      .data_misaligned    ( riscv_core_i.data_misaligned                      ),

      .wb_bypass          ( riscv_core_i.ex_stage_i.branch_in_ex_i            ),

      .wb_valid           ( riscv_core_i.wb_valid                             ),
      .wb_reg_addr        ( riscv_core_i.regfile_waddr_fw_wb_o                ),
      .wb_reg_we          ( riscv_core_i.regfile_we_wb                        ),
      .wb_reg_wdata       ( riscv_core_i.regfile_wdata                        ),

      .imm_u_type         ( riscv_core_i.id_stage_i.imm_u_type                ),
      .imm_uj_type        ( riscv_core_i.id_stage_i.imm_uj_type               ),
      .imm_i_type         ( riscv_core_i.id_stage_i.imm_i_type                ),
      .imm_iz_type        ( riscv_core_i.id_stage_i.imm_iz_type[11:0]         ),
      .imm_z_type         ( riscv_core_i.id_stage_i.imm_z_type                ),
      .imm_s_type         ( riscv_core_i.id_stage_i.imm_s_type                ),
      .imm_sb_type        ( riscv_core_i.id_stage_i.imm_sb_type               ),
      .imm_s2_type        ( riscv_core_i.id_stage_i.imm_s2_type               ),
      .imm_s3_type        ( riscv_core_i.id_stage_i.imm_s3_type               ),
      .imm_vs_type        ( riscv_core_i.id_stage_i.imm_vs_type               ),
      .imm_vu_type        ( riscv_core_i.id_stage_i.imm_vu_type               ),
      .imm_shuffle_type   ( riscv_core_i.id_stage_i.imm_shuffle_type          ),
      .imm_clip_type      ( riscv_core_i.id_stage_i.instr_rdata_i[11:7]       )
    );

    // this handles read to RAM and memory mapped virtual (pseudo) peripherals
    mm_ram #(.RAM_ADDR_WIDTH    (RAM_ADDR_WIDTH),
             .INSTR_RDATA_WIDTH (INSTR_RDATA_WIDTH)
            )
    ram_i
        (.clk_i          ( clknrst_if.clk                 ),
         .rst_ni         ( clknrst_if.reset_n             ),
         .dm_halt_addr_i ( core_cntrl_if.dm_halt_addr     ),

         .instr_req_i    ( instr_req                      ),
         .instr_addr_i   ( instr_addr                     ),
         .instr_rdata_o  ( instr_rdata                    ),
         .instr_rvalid_o ( instr_rvalid                   ),
         .instr_gnt_o    ( instr_gnt                      ),

         .data_req_i     ( data_req                       ),
         .data_addr_i    ( data_addr                      ),
         .data_we_i      ( data_we                        ),
         .data_be_i      ( data_be                        ),
         .data_wdata_i   ( data_wdata                     ),
         .data_rdata_o   ( data_rdata                     ),
         .data_rvalid_o  ( data_rvalid                    ),
         .data_gnt_o     ( data_gnt                       ),

         .irq_id_i       ( 5'b00000                       ),
         .irq_ack_i      ( irq_ack                        ),
         .irq_id_o       ( irq_id_in                      ),
         .irq_o          ( irq                            ),

         .debug_req_o    ( debug_req                      ),

         .pc_core_id_i   ( riscv_core_i.pc_id             ),

         .tests_passed_o ( vp_status_if.tests_passed      ),
         .tests_failed_o ( vp_status_if.tests_failed      ),
         .exit_valid_o   ( vp_status_if.exit_valid        ),
         .exit_value_o   ( vp_status_if.exit_value        )
        ); //ram_i

endmodule : uvmt_cv32_dut_wrap

`endif // __UVMT_CV32_DUT_WRAP_SV__

