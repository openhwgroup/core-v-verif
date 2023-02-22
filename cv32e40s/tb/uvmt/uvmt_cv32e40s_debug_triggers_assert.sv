//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

module uvmt_cv32e40s_debug_trigger_assert
  import uvm_pkg::*;
  import uvma_rvfi_pkg::*;
  import cv32e40s_pkg::*;
  (
    input logic [31:0] dm_halt_addr_i,

    input logic support_debug_mode_q,

    input logic support_if_instr_valid,
    input logic support_id_instr_valid,
    input logic support_ex_instr_valid,
    input logic support_wb_instr_valid,

    input logic [31:0] support_pc_if,
    input logic [31:0] support_pc_id,
    input logic [31:0] support_pc_ex,
    input logic [31:0] support_pc_wb,

    uvma_rvfi_instr_if rvfi_if,
    //uvma_clknrst_if clknrst_if,
    input clk,
    input reset_n,
    uvma_rvfi_csr_if dcsr,
    uvma_rvfi_csr_if dpc,
    uvma_rvfi_csr_if tdata1,
    uvma_rvfi_csr_if tdata2,
    uvma_rvfi_csr_if tdata3,
    uvma_rvfi_csr_if tinfo,
    uvma_rvfi_csr_if tselect,
    uvma_rvfi_csr_if tcontrol

  );
//TODO: legg til beskrivelsen i overview filen til hver assertion
/////////////////////////////////////////////////////////////////////////////////////////

  // Single clock, single reset design, use default clocking
  //default clocking @(posedge clknrst_if.clk); endclocking
  //default disable iff !(clknrst_if.reset_n);
  default clocking @(posedge clk); endclocking
  default disable iff !(reset_n);

  localparam MODE_M = 3;
  localparam MODE_U = 0;

///
logic [31:0] dcsr_r;
logic [31:0] dpc_r;
logic [31:0] tdata1_r;
logic [31:0] tdata2_r;
logic [31:0] tdata3_r;
logic [31:0] tinfo_r;
logic [31:0] tselect_r;
logic [31:0] tcontrol_r;

assign dcsr_r = (dcsr.rvfi_csr_rdata & dcsr.rvfi_csr_rmask);
assign dpc_r = (dpc.rvfi_csr_rdata & dpc.rvfi_csr_rmask);
assign tdata1_r = (tdata1.rvfi_csr_rdata & tdata1.rvfi_csr_rmask);
assign tdata2_r = (tdata2.rvfi_csr_rdata & tdata2.rvfi_csr_rmask);
assign tdata3_r = (tdata3.rvfi_csr_rdata & tdata3.rvfi_csr_rmask);
assign tinfo_r = (tinfo.rvfi_csr_rdata & tinfo.rvfi_csr_rmask);
assign tselect_r = (tselect.rvfi_csr_rdata & tselect.rvfi_csr_rmask);
assign tcontrol_r = (tcontrol.rvfi_csr_rdata & tcontrol.rvfi_csr_rmask);

logic [31:0] dcsr_w;
logic [31:0] dpc_w;
logic [31:0] tdata1_w;
logic [31:0] tdata2_w;
logic [31:0] tdata3_w;
logic [31:0] tinfo_w;
logic [31:0] tselect_w;
logic [31:0] tcontrol_w;

assign dcsr_w = (dcsr.rvfi_csr_wdata & dcsr.rvfi_csr_wmask);
assign dpc_w = (dpc.rvfi_csr_wdata & dpc.rvfi_csr_wmask);
assign tdata1_w = (tdata1.rvfi_csr_wdata); // & tdata1.rvfi_csr_wmask);
assign tdata2_w = (tdata2.rvfi_csr_wdata); // & tdata2.rvfi_csr_wmask);
assign tdata3_w = (tdata3.rvfi_csr_wdata); // & tdata3.rvfi_csr_wmask);
assign tinfo_w = (tinfo.rvfi_csr_wdata & tinfo.rvfi_csr_wmask);
assign tselect_w = (tselect.rvfi_csr_wdata & tselect.rvfi_csr_wmask);
assign tcontrol_w = (tcontrol.rvfi_csr_wdata & tcontrol.rvfi_csr_wmask);
///

  //tdata1_r:
  logic tdata1_m26_load;
  assign tdata1_m26_load = tdata1_r[0];

  logic tdata1_m26_store;
  assign tdata1_m26_store = tdata1_r[1];

  logic tdata1_m26_execute;
  assign tdata1_m26_execute = tdata1_r[2];

  logic tdata1_m26_mode_u_en;
  assign tdata1_m26_mode_u_en = tdata1_r[3];

  logic tdata1_m26_mode_m_en;
  assign tdata1_m26_mode_m_en = tdata1_r[6];

  logic [3:0] tdata1_m26_match;
  assign tdata1_m26_match = tdata1_r[10:7];

  logic [3:0] tdata1_m26_action;
  assign tdata1_m26_action = tdata1_r[15:12];

  logic [3:0] tdata1_type;
  assign tdata1_type = tdata1_r[31:28];


//P:
//instr: PC == tdata2_r
//data: Load_addr == tdata2_r
//Load_addr +1 == tdata2_r
//Load_addr +2 == tdata2_r
//Load_addr +3 == tdata2_r
//
////Kombinasjon: og ikke-sjekker
//- modes
//user mode - alle triggers!
//- matches
//- execute/load/store
//
//
//trigger1
//trigger2
//trigger3
//trigger4
//

  //logic [31:0][4:0] tdata1_arry; //4 + en ekstra kategori
  //logic [31:0][4:0] tdata2_arry; //4 + en ekstra kategori

  logic [4:0][31:0] tdata1_arry; //4 + en ekstra kategori
  logic [4:0][31:0] tdata2_arry; //4 + en ekstra kategori

  always @(posedge clk, negedge reset_n ) begin
    if(!reset_n) begin
      tdata1_arry[0] = 32'hF800_0000;
      tdata1_arry[1] = 32'hF800_0000;
      tdata1_arry[2] = 32'hF800_0000;
      tdata1_arry[3] = 32'hF800_0000;
      tdata1_arry[4] = 32'hF800_0000;
      tdata2_arry = '0;

    end else if (rvfi_if.rvfi_valid) begin
      case(tselect_r)
        32'h0:
          begin
            tdata1_arry[0] = tdata1_r;
            tdata2_arry[0] = tdata2_r;
          end
        32'h1:
          begin
            tdata1_arry[1] = tdata1_r;
            tdata2_arry[1] = tdata2_r;
          end
        32'h2:
          begin
            tdata1_arry[2] = tdata1_r;
            tdata2_arry[2] = tdata2_r;
          end
        32'h3:
          begin
            tdata1_arry[3] = tdata1_r;
            tdata2_arry[3] = tdata2_r;
          end
        default: //never happening!
         begin
            tdata1_arry[4] = tdata1_r;
            tdata2_arry[4] = tdata2_r;
          end
      endcase
    end
  end

  logic [159:0] test_sig1;
  logic [159:0] test_sig2;
  logic [159:0] test_sig3;
  assign test_sig1 = (~(160'h0000_0000_0000_0000_0000_0000_0000_0000_FFFF_FFFF << 1*32) & tdata1_arry);
  assign test_sig2 = ~(160'h0000_0000_0000_0000_0000_0000_0000_0000_FFFF_FFFF << 1*32);
  assign test_sig3 = (160'hF800_0000_F800_0000_F800_0000_F800_0000_0000_0000);

  // This sequence set settings and make sure we are looking at valid rvfi cycle and is not in debug mode
  sequence seq_trigger_execute_settings(csr_trigger_type, csr_instruction_execution, csr_mode_req, csr_match_type, core_mode, core_match);
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_dbg_mode

    && csr_trigger_type

    && csr_instruction_execution
    && csr_mode_req
    && csr_match_type

    && core_mode
    && core_match;
  endsequence

  // This sequence excludes all ways to enter debug mode except from through instruction execution triggering from trigger number <i>
  sequence seq_trigger_execute_no_hit(i);

    // Make sure there is no load/store trigger matches by excluding load/store instructions
    !rvfi_if.rvfi_mem_rmask
    && !rvfi_if.rvfi_mem_wmask

    //TODO: omgjøre denne slik at man sjekker at PC != tdata2[0], [1], [2] of [3]
    // Make sure there can not be a trigger match due to other triggers than trigger number <i>, by disable them
    && ((((~(160'h0000_0000_0000_0000_0000_0000_0000_0000_FFFF_FFFF << i*32)) & tdata1_arry) == 160'hF800_0000_F800_0000_F800_0000_F800_0000_0000_0000)
    || (((~(160'h0000_0000_0000_0000_0000_0000_0000_0000_FFFF_FFFF << i*32)) & tdata1_arry) == 160'hF800_0000_F800_0000_F800_0000_0000_0000_F800_0000)
    || (((~(160'h0000_0000_0000_0000_0000_0000_0000_0000_FFFF_FFFF << i*32)) & tdata1_arry) == 160'hF800_0000_F800_0000_0000_0000_F800_0000_F800_0000)
    || (((~(160'h0000_0000_0000_0000_0000_0000_0000_0000_FFFF_FFFF << i*32)) & tdata1_arry) == 160'hF800_0000_0000_0000_F800_0000_F800_0000_F800_0000))

    ##1 rvfi_if.rvfi_valid[->1]

    // Make sure we do not enter debug mode due to other reasons than trigger matching
    ##0 rvfi_if.rvfi_dbg != 3'h1
    && rvfi_if.rvfi_dbg != 3'h3
    && rvfi_if.rvfi_dbg != 3'h4;
  endsequence

  sequence seq_trigger_hit_or_missmatch_load(trigger_type, operation, mode_req, mode, match_type, match, byte_fetch); //Tar ikke hensyn til push og pop

    //Execute instruction that enter debug mode:
    //TODO: ta hensyn til at man kan ha flere aksesseringer med load store
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_dbg_mode
    //&& !rvfi_if.rvfi_trap //Trengs denne?
    //&& load operation
    && rvfi_if.rvfi_insn[6:0] == 7'b0000011

    && (trigger_type == 4'h2 || trigger_type == 4'h6)

    //trigger x:
    //type
    //&& tdata1_r[x]_m26_execute
    && operation

    //mode
    //&& tdata1_m26_mode_m_en
    //&& rvfi_if.rvfi_mode == MODE_M
    && mode_req
    && mode

    //match
    && match_type
    && byte_fetch
    && match
    //&& ((tdata1_m26_match == 4'h3 && rvfi_if.rvfi_pc_rdata < tdata2_r))

    ##1 rvfi_if.rvfi_valid[->1];
  endsequence

  sequence seq_trigger_hit_or_missmatch_store(trigger_type, operation, mode_req, mode, match_type, match, byte_fetch); //Tar ikke hensyn til push og pop

    //Execute instruction that enter debug mode:
    //TODO: ta hensyn til at man kan ha flere aksesseringer med load store
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_dbg_mode
    //&& !rvfi_if.rvfi_trap //Trengs denne?
    //&& load operation
    && rvfi_if.rvfi_insn[6:0] == 7'b0100011

    && (trigger_type == 4'h2 || trigger_type == 4'h6)

    //trigger x:
    //type
    //&& tdata1_r[x]_m26_execute
    && operation

    //mode
    //&& tdata1_m26_mode_m_en
    //&& rvfi_if.rvfi_mode == MODE_M
    && mode_req
    && mode

    //match
    && match_type
    && byte_fetch
    && match
    //&& ((tdata1_m26_match == 4'h3 && rvfi_if.rvfi_pc_rdata < tdata2_r))

    ##1 rvfi_if.rvfi_valid[->1];
  endsequence

  //Sjekker if:
  generate
    for (genvar i = 0; i < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS; i++) begin

      //operation: execute
      //action: equal
      //mode: machine
      a_dt_hit_execute_eq_m: assert property(
        seq_trigger_execute_settings(

          //tdata csr settings:

          //trigger type is set to 2 or 6
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),

          //instruction execution triggering is enables
          tdata1_arry[i][2],

          //triggering in machine mode is enabled
          tdata1_arry[i][6],

          //There is only a trigger match if address is tdata2
          tdata1_arry[i][10:7] == 4'h0,


          //core conditions:

          //the core is in machine mode
          rvfi_if.rvfi_mode == MODE_M,

          //Make sure there is a match as the address equals tdata2
          rvfi_if.rvfi_pc_rdata == tdata2_arry[i])

        //Check out the next valid instruction
        ##1 rvfi_if.rvfi_valid[->1]

        |->
        //Verify that next instruction is executed from the debug handler
        rvfi_if.rvfi_dbg_mode
      );

      //The following assertions verifyes that debug mode is not entered when not supposed to:
      //The assertions equals the above assertion, except that we have disabled one csr setting and the qualifying core conditions, one at a time
      //we mark the setting that is disabled by marking it with a "//DISABLED" comment
      //In addition we have added an extra sequence that make sure we do not enter debug due to other reasons (see sequence decleration for details)
      //Note that the extra sequence looks for the next valid instruction

      a_dt_hit_execute_eq_m_not_csr_trigger_execution: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          !tdata1_arry[i][2], //DISABLED
          tdata1_arry[i][6],
          tdata1_arry[i][10:7] == 4'h0,
          rvfi_if.rvfi_mode == MODE_M,
          rvfi_if.rvfi_pc_rdata == tdata2_arry[i])

        ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_eq_m_not_csr_mode_req: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          !tdata1_arry[i][6], //DISABLED
          tdata1_arry[i][10:7] == 4'h0,
          rvfi_if.rvfi_mode == MODE_M,
          rvfi_if.rvfi_pc_rdata == tdata2_arry[i])

        ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_eq_m_not_csr_match_type: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][6],
          rvfi_if.rvfi_mode == MODE_M, //FEIL TODO
          !((tdata1_arry[i][10:7] == 4'h0) || tdata1_arry[i][10:7] == 4'h2), //DISABLED
          rvfi_if.rvfi_pc_rdata == tdata2_arry[i])

          ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_eq_m_not_core_match: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][6],
          tdata1_arry[i][10:7] == 4'h0,
          rvfi_if.rvfi_mode == MODE_M,
          !(rvfi_if.rvfi_pc_rdata == tdata2_arry[i])) //DISABLED

          ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );


      //operation: execute
      //action: equal
      //mode: user

      //The following checks do the same checks as above, but in user mode

      a_dt_hit_execute_eq_u: assert property(
        seq_trigger_execute_settings(

          //tdata csr settings:
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][3], //triggering in user mode is enabled (instead of machine mode)
          tdata1_arry[i][10:7] == 4'h0,

          //core conditions:
          rvfi_if.rvfi_mode == MODE_U, //the core is in user mode (instead of machine mode)
          rvfi_if.rvfi_pc_rdata == tdata2_arry[i])

        ##1 rvfi_if.rvfi_valid[->1]
        |->
        rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_eq_u_not_csr_trigger_execution: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          !tdata1_arry[i][2], //DISABLED
          tdata1_arry[i][3],
          tdata1_arry[i][10:7] == 4'h0,
          rvfi_if.rvfi_mode == MODE_U,
          rvfi_if.rvfi_pc_rdata == tdata2_arry[i])

        ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_eq_u_not_csr_mode_req: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          !tdata1_arry[i][3], //DISABLED
          tdata1_arry[i][10:7] == 4'h0,
          rvfi_if.rvfi_mode == MODE_U,
          rvfi_if.rvfi_pc_rdata == tdata2_arry[i])

        ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_eq_u_not_csr_match_type: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][3],
          rvfi_if.rvfi_mode == MODE_U,
          !((tdata1_arry[i][10:7] == 4'h0) || tdata1_arry[i][10:7] == 4'h2), //DISABLED
          rvfi_if.rvfi_pc_rdata == tdata2_arry[i])

          ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_eq_u_not_core_match: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][3],
          tdata1_arry[i][10:7] == 4'h0,
          rvfi_if.rvfi_mode == MODE_U,
          !(rvfi_if.rvfi_pc_rdata == tdata2_arry[i])) //DISABLED

          ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      //operation: execute
      //action: greater or equal
      //mode: machine

      //The following assertions check instruction execution triggering when the address must be greater or equal to tdata2
      //The following assertions are similar to those above, with a minor change
      //The first part of assertions checks machine mode and the second part checks user mode

      a_dt_hit_execute_greater_eq_m: assert property(
        seq_trigger_execute_settings(

          //tdata csr settings:
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][6], //triggering in machine mode is enabled
          tdata1_arry[i][10:7] == 4'h2, //There is only a trigger match if address is greater or equal tdata2

          //core conditions:
          rvfi_if.rvfi_mode == MODE_M, //the core is in machine mode
          rvfi_if.rvfi_pc_rdata >= tdata2_arry[i]) //Make sure there is a match as the address is greater or equal tdata2

        ##1 rvfi_if.rvfi_valid[->1]
        |->
        rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_greater_eq_m_not_csr_trigger_execution: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          !tdata1_arry[i][2], //DISABLED
          tdata1_arry[i][6],
          tdata1_arry[i][10:7] == 4'h2,
          rvfi_if.rvfi_mode == MODE_M,
          rvfi_if.rvfi_pc_rdata >= tdata2_arry[i])

        ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_greater_eq_m_not_csr_mode_req: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          !tdata1_arry[i][6], //DISABLED
          tdata1_arry[i][10:7] == 4'h2,
          rvfi_if.rvfi_mode == MODE_M,
          rvfi_if.rvfi_pc_rdata >= tdata2_arry[i])

        ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_greater_eq_m_not_csr_match_type: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][6],
          rvfi_if.rvfi_mode == MODE_M,
          !((tdata1_arry[i][10:7] == 4'h0) || tdata1_arry[i][10:7] == 4'h2), //DISABLED
          rvfi_if.rvfi_pc_rdata >= tdata2_arry[i])

          ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_greater_eq_m_not_core_match: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][6],
          tdata1_arry[i][10:7] == 4'h2,
          rvfi_if.rvfi_mode == MODE_M,
          !(rvfi_if.rvfi_pc_rdata >= tdata2_arry[i])) //DISABLED

          ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      //operation: execute
      //action: greater or equal
      //mode: user

      a_dt_hit_execute_greater_eq_u: assert property(
        seq_trigger_execute_settings(

          //tdata csr settings:
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][3], //triggering in user mode is enabled
          tdata1_arry[i][10:7] == 4'h2,

          //core conditions:
          rvfi_if.rvfi_mode == MODE_U, //the core is in user mode
          rvfi_if.rvfi_pc_rdata >= tdata2_arry[i])

        ##1 rvfi_if.rvfi_valid[->1]
        |->
        rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_greater_eq_u_not_csr_trigger_execution: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          !tdata1_arry[i][2], //DISABLED
          tdata1_arry[i][3],
          tdata1_arry[i][10:7] == 4'h2,
          rvfi_if.rvfi_mode == MODE_U,
          rvfi_if.rvfi_pc_rdata >= tdata2_arry[i])

        ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_greater_eq_u_not_csr_mode_req: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          !tdata1_arry[i][3], //DISABLED
          tdata1_arry[i][10:7] == 4'h2,
          rvfi_if.rvfi_mode == MODE_U,
          rvfi_if.rvfi_pc_rdata >= tdata2_arry[i])

        ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_greater_eq_u_not_csr_match_type: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][3],
          rvfi_if.rvfi_mode == MODE_U,
          !((tdata1_arry[i][10:7] == 4'h0) || tdata1_arry[i][10:7] == 4'h2), //DISABLED
          rvfi_if.rvfi_pc_rdata >= tdata2_arry[i])

          ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_greater_eq_u_not_core_match: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][3],
          tdata1_arry[i][10:7] == 4'h2,
          rvfi_if.rvfi_mode == MODE_U,
          !(rvfi_if.rvfi_pc_rdata >= tdata2_arry[i])) //DISABLED

          ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      //operation: execute
      //action: lesser
      //mode: machine

      //The following assertions check instruction execution triggering when the address must be lesser than tdata2
      //The following assertions are similar to those above, with a minor change
      //The first part of assertions checks machine mode and the second part checks user mode

      a_dt_hit_execute_lesser_m: assert property(
        seq_trigger_execute_settings(

          //tdata csr settings:
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][6], //triggering in machine mode is enabled
          tdata1_arry[i][10:7] == 4'h3, //There is only a trigger match if address is lesser tdata2

          //core conditions:
          rvfi_if.rvfi_mode == MODE_M, //the core is in machine mode
          rvfi_if.rvfi_pc_rdata < tdata2_arry[i]) //Make sure there is a match as the address is lesser tdata2

        ##1 rvfi_if.rvfi_valid[->1]
        |->
        rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_lesser_m_not_csr_trigger_execution: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          !tdata1_arry[i][2], //DISABLED
          tdata1_arry[i][6],
          tdata1_arry[i][10:7] == 4'h3,
          rvfi_if.rvfi_mode == MODE_M,
          rvfi_if.rvfi_pc_rdata < tdata2_arry[i])

        ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_lesser_m_not_csr_mode_req: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          !tdata1_arry[i][6], //DISABLED
          tdata1_arry[i][10:7] == 4'h3,
          rvfi_if.rvfi_mode == MODE_M,
          rvfi_if.rvfi_pc_rdata < tdata2_arry[i])

        ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_lesser_m_not_csr_match_type: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][6],
          rvfi_if.rvfi_mode == MODE_M,
          !(tdata1_arry[i][10:7] == 4'h3), //DISABLED
          rvfi_if.rvfi_pc_rdata < tdata2_arry[i])

          ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_lesser_m_not_core_match: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][6],
          tdata1_arry[i][10:7] == 4'h3,
          rvfi_if.rvfi_mode == MODE_M,
          !(rvfi_if.rvfi_pc_rdata < tdata2_arry[i])) //DISABLED

          ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      //operation: execute
      //action: lesser
      //mode: user

      a_dt_hit_execute_lesser_u: assert property(
        seq_trigger_execute_settings(

          //tdata csr settings:
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][3], //triggering in user mode is enabled
          tdata1_arry[i][10:7] == 4'h3,

          //core conditions:
          rvfi_if.rvfi_mode == MODE_U, //the core is in user mode
          rvfi_if.rvfi_pc_rdata < tdata2_arry[i])

        ##1 rvfi_if.rvfi_valid[->1]
        |->
        rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_lesser_u_not_csr_trigger_execution: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          !tdata1_arry[i][2], //DISABLED
          tdata1_arry[i][3],
          tdata1_arry[i][10:7] == 4'h3,
          rvfi_if.rvfi_mode == MODE_U,
          rvfi_if.rvfi_pc_rdata < tdata2_arry[i])

        ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_lesser_u_not_csr_mode_req: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          !tdata1_arry[i][3], //DISABLED
          tdata1_arry[i][10:7] == 4'h3,
          rvfi_if.rvfi_mode == MODE_U,
          rvfi_if.rvfi_pc_rdata < tdata2_arry[i])

        ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_lesser_u_not_csr_match_type: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][3],
          rvfi_if.rvfi_mode == MODE_U,
          !(tdata1_arry[i][10:7] == 4'h3), //DISABLED
          rvfi_if.rvfi_pc_rdata < tdata2_arry[i])

          ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      a_dt_hit_execute_lesser_u_not_core_match: assert property(
        seq_trigger_execute_settings(
          (tdata1_arry[i][31:28] == 4'h2 || tdata1_arry[i][31:28] == 4'h6),
          tdata1_arry[i][2],
          tdata1_arry[i][3],
          tdata1_arry[i][10:7] == 4'h3,
          rvfi_if.rvfi_mode == MODE_U,
          !(rvfi_if.rvfi_pc_rdata < tdata2_arry[i])) //DISABLED

          ##0 seq_trigger_execute_no_hit(i)

        |->
        !rvfi_if.rvfi_dbg_mode
      );

      //operation: load
      //action: equal
      //mode: machine
      a_dt_hit_load_eq_m_byte0: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[0]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_eq_m_byte1: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr+1 == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[1]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_eq_m_byte2: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr+2 == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[2]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_eq_m_byte3: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr+3 == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[3]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );

      //operation: load
      //action: equal
      //mode: user
      a_dt_hit_load_eq_u_byte0: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type - constant
          tdata1_arry[i][0], //operation - constant
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr+1 == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[0]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_eq_u_byte1: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr+1 == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[1]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_eq_u_byte2: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr+2 == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[2]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_eq_u_byte3: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr+3 == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[3]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      //operation: load
      //action: greater or equal
      //mode: machine
      a_dt_hit_load_greater_m_byte0: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type - constant
          tdata1_arry[i][0], //operation - constant
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[0])
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_greater_m_byte1: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+1 >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[1]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_greater_m_byte2: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+2 >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[2]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_greater_m_byte3: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+3 >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[3]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      //operation: load
      //action: greater or equal
      //mode: user
      a_dt_hit_load_greater_u_byte0: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type - constant
          tdata1_arry[i][0], //operation - constant
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_pc_rdata >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[0]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_greater_u_byte1: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+1 >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[1]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_greater_u_byte2: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+2 >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[2]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_greater_u_byte3: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+3 >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[3]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      //operation: load
      //action: lesser
      //mode: machine
      a_dt_hit_load_lesser_m_byte0: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type - constant
          tdata1_arry[i][0], //operation - constant
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h3, //match_type
          rvfi_if.rvfi_pc_rdata < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[0]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_lesser_m_byte1: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+1 < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[1]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_lesser_m_byte2: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+2 < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[2]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_lesser_m_byte3: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+3 < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[3]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      //operation: load
      //action: lesser
      //mode: user
      a_dt_hit_load_lesser_u_byte0: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type - constant
          tdata1_arry[i][0], //operation - constant
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h3, //match_type
          rvfi_if.rvfi_pc_rdata < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[0])
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_lesser_u_byte1: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+1 < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[1]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_lesser_u_byte2: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+2 < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[2]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_load_lesser_u_byte3: assert property(
        seq_trigger_hit_or_missmatch_load(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][0], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+3 < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_rmask[3]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      //operation: load
      //action: equal
      //mode: machine
      a_dt_hit_store_eq_m_byte0: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[0]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_eq_m_byte1: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr+1 == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[1]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_eq_m_byte2: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr+2 == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[2]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_eq_m_byte3: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr+3 == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[3]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );

      //operation: load
      //action: equal
      //mode: user
      a_dt_hit_store_eq_u_byte0: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type - constant
          tdata1_arry[i][1], //operation - constant
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr+1 == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[0]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_eq_u_byte1: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr+1 == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[1]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_eq_u_byte2: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr+2 == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[2]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_eq_u_byte3: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h0, //match_type
          rvfi_if.rvfi_mem_addr+3 == tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[3]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      //operation: load
      //action: greater or equal
      //mode: machine
      a_dt_hit_store_greater_m_byte0: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type - constant
          tdata1_arry[i][1], //operation - constant
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[0])
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_greater_m_byte1: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+1 >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[1]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_greater_m_byte2: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+2 >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[2]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_greater_m_byte3: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+3 >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[3]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      //operation: load
      //action: greater or equal
      //mode: user
      a_dt_hit_store_greater_u_byte0: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type - constant
          tdata1_arry[i][1], //operation - constant
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_pc_rdata >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[0]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_greater_u_byte1: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+1 >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[1]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_greater_u_byte2: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+2 >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[2]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_greater_u_byte3: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+3 >= tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[3]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      //operation: load
      //action: lesser
      //mode: machine
      a_dt_hit_store_lesser_m_byte0: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type - constant
          tdata1_arry[i][1], //operation - constant
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h3, //match_type
          rvfi_if.rvfi_pc_rdata < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[0]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_lesser_m_byte1: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+1 < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[1]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_lesser_m_byte2: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+2 < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[2]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_lesser_m_byte3: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][6], //mode_req
          rvfi_if.rvfi_mode == MODE_M, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+3 < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[3]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      //operation: load
      //action: lesser
      //mode: user
      a_dt_hit_store_lesser_u_byte0: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type - constant
          tdata1_arry[i][1], //operation - constant
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h3, //match_type
          rvfi_if.rvfi_pc_rdata < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[0])
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_lesser_u_byte1: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+1 < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[1]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_lesser_u_byte2: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+2 < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[2]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );
      a_dt_hit_store_lesser_u_byte3: assert property(
        seq_trigger_hit_or_missmatch_store(
          tdata1_arry[i][31:28], //trigger_type
          tdata1_arry[i][1], //operation
          tdata1_arry[i][3], //mode_req
          rvfi_if.rvfi_mode == MODE_U, //mode
          tdata1_arry[i][10:7] == 4'h2, //match_type
          rvfi_if.rvfi_mem_addr+3 < tdata2_arry[i], //match
          rvfi_if.rvfi_mem_wmask[3]) //memory_fetch
        |->
        rvfi_if.rvfi_dbg_mode
      );

    end
  endgenerate

//sjekker if not:


// P1:

//3) & 4) & 5) & 6)
  logic [31:0] support_pc_q1;
  logic [31:0] enter_debug_PC;
  logic pc_dm_addr_match_half_sticky;

  always @(posedge clk) begin
      if (support_wb_instr_valid) begin
      support_pc_q1 <= support_pc_wb;

      end else if(support_ex_instr_valid) begin
      support_pc_q1 <= support_pc_ex;

      end else if(support_id_instr_valid) begin
      support_pc_q1 <= support_pc_id;

      end else begin
      support_pc_q1 <= support_pc_if;
      end

    if(support_pc_if == dm_halt_addr_i && $rose(support_debug_mode_q)) begin //Nå vet vi at vi har entered debug.
      pc_dm_addr_match_half_sticky = 1;
      enter_debug_PC = support_pc_q1;
    end
    if (rvfi_if.rvfi_valid) begin
      pc_dm_addr_match_half_sticky <= 0;
    end
  end


  a_dt_debug_state_initialization: assert property (
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap
    && $rose(rvfi_if.rvfi_dbg_mode)
    |->
    dcsr_r[8:6] == rvfi_if.rvfi_dbg
    && rvfi_if.rvfi_pc_rdata == dm_halt_addr_i
    && dpc_r == enter_debug_PC
  );


// P2:
// P3:

//1)
  a_dt_0_triggers_tdata1_access: assert property (
    rvfi_if.rvfi_valid
    && uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS == '0
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[14:12] != '0
    && (rvfi_if.rvfi_insn[31:20] == 12'h7A0 //tselect_r ??
    || rvfi_if.rvfi_insn[31:20] == 12'h7A1 //tdata1_r
    || rvfi_if.rvfi_insn[31:20] == 12'h7A2 //tdata2_r
    || rvfi_if.rvfi_insn[31:20] == 12'h7A3 //tdata3_r
    || rvfi_if.rvfi_insn[31:20] == 12'h7A4 //tinfo_r ??
    || rvfi_if.rvfi_insn[31:20] == 12'h7A4) //tcontrol_r ??
    && rvfi_if.rvfi_trap.exception_cause != 6'h1
    && rvfi_if.rvfi_trap.exception_cause != 6'h18
    && rvfi_if.rvfi_trap.exception_cause != 6'h19
    |->
    rvfi_if.rvfi_trap.trap
    && rvfi_if.rvfi_trap.exception
    && (rvfi_if.rvfi_trap.exception_cause == 6'h2)
  );

//2) & 3)
  a_dt_0_triggers_tselect_is_0_and_no_triggering: assert property (
    rvfi_if.rvfi_valid
    && uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS == '0
    |->
    tselect_r == '0
    && rvfi_if.rvfi_dbg != 3'h2
  );


// P4:

//1)

  property p_all_trigger(tselect_val, tdata1_type_val);
    tselect_r == tselect_val
    && tdata1_type == tdata1_type_val;
  endproperty

  generate
    for (genvar tselect_val = 0; tselect_val < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS; tselect_val++) begin

      a_trigger_i_has_type_mcontrol: cover property(
        p_all_trigger(tselect_val, 4'h2)
      );

      a_trigger_i_has_type_mcontrol6: cover property(
        p_all_trigger(tselect_val, 4'h6)
      );

      a_trigger_i_has_type_etrigger: cover property(
        p_all_trigger(tselect_val, 4'h5)
      );

      a_trigger_i_has_type_disable: cover property(
        p_all_trigger(tselect_val, 4'hF)
      );

    end
  endgenerate

//2) TODO!

//3)

  a_dt_tselect_higher_than_dbg_num_triggers: assert property(
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[13:12] != '0
    && rvfi_if.rvfi_insn[31:20] == 12'h7A0 //tselect_r
    |->
    rvfi_if.rvfi_rd1_wdata < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS
  );


//4)

  a_dt_access_context: assert property (
    rvfi_if.rvfi_valid
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[14:12] != '0
    && (rvfi_if.rvfi_insn[31:20] == 12'h7A8 //mcontext
    || rvfi_if.rvfi_insn[31:20] == 12'h7AA //mscontext
    || rvfi_if.rvfi_insn[31:20] == 12'h6A8 //hcontext
    || rvfi_if.rvfi_insn[31:20] == 12'h5A8) //scontext
    |->
    rvfi_if.rvfi_trap.trap
  );

// P5:

//4)
  ///mcontrol
  a_dt_tie_offs_tdata1_mcontrol: assert property (
    rvfi_if.rvfi_valid
    && tdata1_type == 4'h2
    |->
    tdata1_r[27]
    && !tdata1_r[26:21]
    && !tdata1_r[20]
    && !tdata1_r[19]
    && !tdata1_r[18]
    && !tdata1_r[17:16]
    && tdata1_m26_action == 4'h1
    && !tdata1_r[11]
    && !tdata1_r[5]
    && !tdata1_r[4]
  );

  //mcontrol6
  a_dt_tie_offs_tdata1_mcontrol6: assert property (
    rvfi_if.rvfi_valid
    && tdata1_type == 4'h6
    |->
    tdata1_r[27]
    && !tdata1_r[26:25]
    && !tdata1_r[24]
    && !tdata1_r[23]
    && !tdata1_r[22]
    && !tdata1_r[21]
    && !tdata1_r[20]
    && !tdata1_r[19:16]
    && tdata1_m26_action == 4'h1
    && !tdata1_r[11]
    && !tdata1_r[5]
    && !tdata1_r[4]
  );

  //etrigger
  a_dt_tie_offs_tdata1_etrigger: assert property (
    rvfi_if.rvfi_valid
    && tdata1_type == 4'h5
    |->
    tdata1_r[27]
    && !tdata1_r[26]
    && !tdata1_r[25:13]
    && !tdata1_r[12]
    && !tdata1_r[11]
    && !tdata1_r[10]
    && !tdata1_r[8]
    && !tdata1_r[7]
    && tdata1_r[5:0] == 6'h1
  );

  //disabled
  a_dt_tie_offs_tdata1_disabled: assert property (
    rvfi_if.rvfi_valid
    && tdata1_type == 4'hF
    |->
    tdata1_r[27]
    && !tdata1_r[26:0]
  );

  a_dt_tie_offs_tdata3: assert property (
    rvfi_if.rvfi_valid
    |->
    tdata3_r == '0
  );

  a_dt_tie_offs_tinfo: assert property (
    rvfi_if.rvfi_valid
    |->
    tinfo_r[31:16] == '0
  );

  a_dt_tie_offs_tcontrol: assert property (
    rvfi_if.rvfi_valid
    |->
    tcontrol_r[31:8] == '0
    && tcontrol_r[6:4] == '0
    && tcontrol_r[2:0] == '0
  );

// P6:
// P7:
//instr: PC == tdata2_r
//data: Load_addr == tdata2_r
//Load_addr +1 == tdata2_r
//Load_addr +2 == tdata2_r
//Load_addr +3 == tdata2_r


// P8:
// P9:
// P10:

  a_dt_tdata1_types: assert property (
    rvfi_if.rvfi_valid
    |->
    tdata1_type == 4'h2
    || tdata1_type == 4'h5
    || tdata1_type == 4'h6
    || tdata1_type == 4'hF
  );

// P11:

//1)
  a_dt_access_csr_not_dbg_mode: assert property (
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_dbg_mode
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[13:12] == 2'b00
    && (rvfi_if.rvfi_insn[31:20] == 12'h7A1 //tdata1_r
    || rvfi_if.rvfi_insn[31:20] == 12'h7A2 //tdata2_r
    || rvfi_if.rvfi_insn[31:20] == 12'h7A3) //tdata3_r
    |->
     !tdata1.rvfi_csr_wmask
    && !tdata2.rvfi_csr_wmask
    && !tdata3.rvfi_csr_wmask
  );

//2)
  a_dt_dmode: assert property (
    rvfi_if.rvfi_valid
    && rvfi_if.rvfi_dbg_mode //usikker på om denne må være høy hvis man antar ingen trap - jo fordi uten dbg mode får man bare en instruksjon som ikke gjør noe, men ingen trap
    && !rvfi_if.rvfi_trap.trap //Usikker på om dette gir trap
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[13:12] != 2'h0
    && !rvfi_if.rvfi_insn[14] //Kan ikke bruke immediate CSR operasjoner

    && rvfi_if.rvfi_insn[31:20] == 12'h7A1 //tdata1_r

    //immediate
    //&& (rvfi_if.rvfi_insn[14] //Not big enough to write to the whole register I believe.

    //rs:
    //|| (!rvfi_if.rvfi_insn[14]
    //TODO: dette kan legges inn under en cover istedenfor:
    && ((rvfi_if.rvfi_insn[13:12] == 2'h01
    && !rvfi_if.rvfi_rs1_rdata[27])

    || rvfi_if.rvfi_insn[13:12] == 2'h11
    && rvfi_if.rvfi_rs1_rdata[27])

    //&& rvfi_if.rvfi_insn[13:12] != 2'h11
    //&& rvfi_if.rvfi_rs1_rdata[27] //))

    |->
    tdata1_w[27]
  );


// P12:

//1)
  a_dt_0_triggers_tinfo: assert property (
    rvfi_if.rvfi_valid
    && uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS == '0
    |->
    !tinfo_r
  );

  a_dt_triggers_tinfo: assert property (
    rvfi_if.rvfi_valid
    && uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS != '0
    |->
    !tinfo_r[1:0]
    && tinfo_r[2]
    && !tinfo_r[4:3]
    && tinfo_r[5]
    && tinfo_r[6]
    && !tinfo_r[14:7]
    && tinfo_r[15]
    && !tinfo_r[31:16]
  );


//2)

// P13:

// P14:

  a_dt_warl_tselect: assert property ( //TODO: allerede assertion for dette
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap //Usikker på om dette gir trap
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[13:12] != '0
    && rvfi_if.rvfi_insn[31:20] == 12'h7A0 //tselect_r
    |->
    tselect_w < uvmt_cv32e40s_pkg::CORE_PARAM_DBG_NUM_TRIGGERS
    || tselect_w == '0 //in case there is no triggers
  );


  a_dt_warl_tdata1_general: assert property (
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap //Usikker på om dette gir trap
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[13:12] != '0
    && rvfi_if.rvfi_insn[31:20] == 12'h7A1 //tdata
    |->
    (tdata1_w[31:28] == 4'h2
    || tdata1_w[31:28] == 4'h5
    || tdata1_w[31:28] == 4'h6
    || tdata1_w[31:28] == 4'hF)
    && tdata1_w[27]
  );

  a_dt_warl_tdata1_m2: assert property (
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap //Usikker på om dette gir trap
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[13:12] != '0
    && rvfi_if.rvfi_insn[31:20] == 12'h7A1 //tdata
    && tdata1_w[31:28] == 4'h2
    |->
    tdata1_w[26:21] == '0
    && tdata1_w[20] == '0
    && tdata1_w[19] == '0
    && tdata1_w[18] == '0
    && tdata1_w[17:16] == '0
    && tdata1_w[15:12] == 4'h1
    && tdata1_w[11] == '0
    && (tdata1_w[10:7] == '0
    || tdata1_w[10:7] == 4'h2
    || tdata1_w[10:7] == 4'h3)
    && tdata1_w[5] == '0
    && tdata1_w[4] == '0
  );

  a_dt_warl_tdata1_m6: assert property (
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap //Usikker på om dette gir trap
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[13:12] != '0
    && rvfi_if.rvfi_insn[31:20] == 12'h7A1 //tdata
    && tdata1_w[31:28] == 4'h6
    |->
    tdata1_w[26:25] == '0
    && tdata1_w[24] == '0
    && tdata1_w[23] == '0
    && tdata1_w[22] == '0
    && tdata1_w[21] == '0
    && tdata1_w[20] == '0
    && tdata1_w[19:16] == '0
    && tdata1_w[15:12] == 4'h1
    && tdata1_w[11] == '0
    && (tdata1_w[10:7] == '0
    || tdata1_w[10:7] == 4'h2
    || tdata1_w[10:7] == 4'h3)
    && tdata1_w[5] == '0
    && tdata1_w[4] == '0
  );

  a_dt_warl_tdata1_etrigger: assert property (
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap //Usikker på om dette gir trap
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[13:12] != '0
    && rvfi_if.rvfi_insn[31:20] == 12'h7A1 //tdata
    && tdata1_w[31:28] == 4'h5
    |->
    tdata1_w[26] == '0
    && tdata1_w[25:13] == '0
    && tdata1_w[12] == '0
    && tdata1_w[11] == '0
    && tdata1_w[10] == '0
    && tdata1_w[8] == '0
    && tdata1_w[7] == '0
    && tdata1_w[5:0] == 6'h1
  );

  a_dt_warl_tdata1_disabled: assert property (
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap //Usikker på om dette gir trap
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[13:12] != '0
    && rvfi_if.rvfi_insn[31:20] == 12'h7A1 //tdata
    && tdata1_w[31:28] == 4'hF
    |->
    tdata1_w[26:0] == '0
  );

  a_dt_warl_tdata2_etrigger: assert property (
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap //Usikker på om dette gir trap
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[13:12] != '0
    && rvfi_if.rvfi_insn[31:20] == 12'h7A2 //tdata2_r
    && tdata1_w[31:28] == 4'h5
    |->
    tdata2_w[23:12] == '0
    && tdata2_w[10:9] == '0
    && tdata2_w[6] == '0
    && tdata2_w[4] == '0
    && tdata2_w[0] == '0
  );

  a_dt_warl_tdata3: assert property (
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap //Usikker på om dette gir trap
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[13:12] != '0
    && rvfi_if.rvfi_insn[31:20] == 12'h7A3 //tdata3_r
    |->
    tdata3_w == '0
  );

  a_dt_warl_tinfo: assert property (
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap //Usikker på om dette gir trap
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[13:12] != '0
    && rvfi_if.rvfi_insn[31:20] == 12'h7A4 //tinfo_r
    |->
    tinfo_w[31:16] == '0
  );

  a_dt_warl_tcontrol: assert property (
    rvfi_if.rvfi_valid
    && !rvfi_if.rvfi_trap.trap //Usikker på om dette gir trap
    && rvfi_if.rvfi_insn[6:0] == OPCODE_SYSTEM
    && rvfi_if.rvfi_insn[13:12] != '0
    && rvfi_if.rvfi_insn[31:20] == 12'h7A5 //tcontrol_r
    |->
    tcontrol_w[31:8] == '0
    && tcontrol_w[7] == '0
    && tcontrol_w[6:4] == '0
    && tcontrol_w[3] == '0
    && tcontrol_w[2:0] == '0
  );




endmodule : uvmt_cv32e40s_debug_trigger_assert
