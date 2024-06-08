///////////////////////////////////////////////////////////////////////////////
//
// Copyright 2023 OpenHW Group
// Copyright 2023 Dolphin Design
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
// SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0
//*******************************************************************************************************************************************

// Note: 
// 1) This coverage model complements Imperas coverage XPULPV2 with addtional coverage collection related to hwloops
// 2) It uses uvmt_cv32e40p_rvvi_if
// 3) Has covergroup for hwloops csr setup registers
// 4) Has covergroup for hwloops features and events within hwloops such as exception, irq and debug entry (debug covers haltreq, trigger, ebreakm, step)
// 5) Improvement[Optional]: hwloop_stat_sub for handle (irq/debug) implementation

`ifndef UVME_RV32X_HWLOOP_COVG
`define UVME_RV32X_HWLOOP_COVG

class uvme_rv32x_hwloop_covg # (
  parameter int ILEN    = 32,
  parameter int XLEN    = 32
) extends uvm_component;

  localparam SKIP_RVVI_INIT_VALID_CNT = 1;
  localparam HWLOOP_NB = 2;
  localparam CSR_LPSTART0_ADDR = 32'hCC0;
  localparam CSR_LPEND0_ADDR   = 32'hCC1;
  localparam CSR_LPCOUNT0_ADDR = 32'hCC2;
  localparam INSTR_CBREAK      = 32'h9002;
  localparam INSN_ILLEGAL      = 32'hFFFFFFFF; // user-defined for any illegal insn that leads to illegal exception
  localparam INSN_EBREAKM      = 32'hFFFFFFFE; // user-defined

  typedef enum bit [1:0] {NULL_TYPE=0, SINGLE, NESTED}          hwloop_type_t;
  typedef enum bit [1:0] {NULL_SETUP=0, SHORT, LONG}            hwloop_setup_t;
  typedef enum int {EXCP_EBREAK=0, EXCP_ECALL, EXCP_ILLEGAL, 
                    IS_IRQ, DBG_HALTREQ, DBG_EBREAKM, DBG_TRIG, 
                    DBG_STEP, MC_INSN, TOTAL_EVENT=9}           hwloop_evt_t;
  typedef enum int {LOC_LPSTART=0, LOC_LPSTART_P4, 
                    LOC_LPEND, LOC_LPEND_M4, 
                    LOC_OTHERS, TOTAL_LOC=5}                    hwloop_evt_loc_t;

  typedef struct {
    bit [31:0] lp_start     [HWLOOP_NB];
    bit [31:0] lp_end       [HWLOOP_NB];
    bit [31:0] lp_count     [HWLOOP_NB];
    bit        lp_start_wb  [HWLOOP_NB];
    bit        lp_end_wb    [HWLOOP_NB];
    bit        lp_count_wb  [HWLOOP_NB];
  } s_csr_hwloop;
  typedef struct {
    hwloop_type_t         hwloop_type;
    hwloop_setup_t        hwloop_setup            [HWLOOP_NB];
    s_csr_hwloop          hwloop_csr;
    bit                   sample_hwloop_csr_done  [HWLOOP_NB];
    bit                   execute_instr_in_hwloop [HWLOOP_NB];
    int                   track_lp_cnt            [HWLOOP_NB];
    int unsigned          dbg_haltreq_cnt         [HWLOOP_NB];
    int unsigned          dbg_ebreakm_cnt         [HWLOOP_NB];
    int unsigned          dbg_trigger_cnt         [HWLOOP_NB];
    int unsigned          dbg_step_cnt            [HWLOOP_NB];
    int unsigned          excp_ebreak_cnt         [HWLOOP_NB];
    int unsigned          excp_ecall_cnt          [HWLOOP_NB];
    int unsigned          excp_illegal_cnt        [HWLOOP_NB];
  } s_hwloop_stat;
  typedef struct {
    bit               en_cov_irq                  ;
    bit               en_cov_dbg_haltreq          ;
    bit               en_cov_dbg_ebreakm          ;
    bit               en_cov_dbg_trigger          ;
    bit               en_cov_dbg_step_cnt         ;
    bit               en_cov_dbg_step_cnt_loc     ;
    bit               en_cov_excp_ebreak          ;
    bit               en_cov_excp_ecall           ;
    bit               en_cov_excp_illegal         ;
    bit               en_cov_mc_insn              ;
    bit               en_cov_insn                 ;
    bit               en_cov_event_loc            ;
  } s_hwloop_cov;

  // PROPERTIES - START

  `define DEF_LOCAL_VARS(TYPE) \
  local s_csr_hwloop        csr_hwloop_``TYPE                 = '{default:0}; \
  local s_hwloop_stat       hwloop_stat_``TYPE                = '{default:0, hwloop_type:NULL_TYPE, hwloop_setup:'{default:NULL_SETUP}}; \
  local logic [31:0]        prev_pc_rdata_``TYPE              = '{default:0}; \
  local hwloop_evt_loc_t    hwloop_evt_loc_``TYPE             [HWLOOP_NB][hwloop_evt_t][$]; \
  local bit [(ILEN-1):0]    insn_list_in_hwloop_``TYPE        [HWLOOP_NB][$]; \
  local bit [(ILEN-1):0]    mc_insn_list_in_hwloop_``TYPE     [HWLOOP_NB][$]; \
  local bit [31:0]          irq_vect_``TYPE                   [HWLOOP_NB][$]; \
  local bit                 lpend_has_pending_irq_``TYPE      [HWLOOP_NB] = '{default:0}; \
  local bit                 done_insn_list_capture_``TYPE     [HWLOOP_NB] = '{default:0}; \
  local bit                 done_insn_list_capture_d1_``TYPE  [HWLOOP_NB] = '{default:0}; \
  local s_hwloop_cov        hwloop_cov_``TYPE                 [HWLOOP_NB] = '{default:0};
  
  `DEF_LOCAL_VARS(main)
  `DEF_LOCAL_VARS(sub)
  `DEF_LOCAL_VARS(init)

  virtual       uvmt_cv32e40p_rvvi_if #( .XLEN(XLEN), .ILEN(ILEN)) cv32e40p_rvvi_vif;
  string        _header = "XPULPV2_HWLOOP_COV";
  bit           en_cvg_sampling = 1;
  bit           in_nested_loop0 = 0, in_nested_loop0_d1 = 0;
  bit           is_ebreak = 0, is_ebreakm = 0, is_ecall = 0, is_illegal = 0, is_irq = 0, is_dbg_mode = 0, is_mc_insn = 0;
  bit           is_trap = 0; // trap any period that is redundant due to handling entry which causes data flush
  bit           has_pending_trap_due2_dbg = 0;    // has trap pending due to debug mode entry
  bit           has_trap_due2_dbg_match_trig = 0; // has trap due to debug trigger match
  bit           has_pending_trap_due2_irq = 0;    // has trap pending due to irq entry
  bit           enter_hwloop_sub = 0;
  int           enter_hwloop_sub_cnt = 0;
  bit           pending_irq = 0;
  bit           pending_irq_ack = 0;
  logic [31:0]  valid_irq_prev = 32'h0;
  logic [31:0]  prev_irq_onehot_priority = 0, prev_irq_onehot_priority_always = 0;
  bit           prev_irq_onehot_priority_is_0 = 0;

  dcsr_cause_t      dcsr_cause;
  exception_code_t  exception_code;

  // PROPERTIES - END

  // COVERGROUPS DEFINE HERE - START

  `define CG_CSR_HWLOOP(LOOP_IDX) cg_csr_hwloop_``LOOP_IDX``
  `define DEF_CG_CSR_HWLOOP(LOOP_IDX) covergroup cg_csr_hwloop_``LOOP_IDX with function sample(s_csr_hwloop csr_hwloop); \
    option.per_instance         = 1; \
    `ifdef MODEL_TECH \
    option.get_inst_coverage    = 1; \
    `endif \
    type_option.merge_instances = 1; \
    cp_lpstart_``LOOP_IDX : coverpoint (csr_hwloop.lp_start[``LOOP_IDX``]) iff (csr_hwloop.lp_start_wb[``LOOP_IDX``] && csr_hwloop.lp_end_wb[``LOOP_IDX``] && csr_hwloop.lp_count_wb[``LOOP_IDX``]) { \
      bins lpstart_range_0      = {[32'h0000_03FC : 32'h0000_0004]}; \
      bins lpstart_range_1      = {[32'h0000_0FFC : 32'h0000_0400]}; \
      bins lpstart_range_2      = {[32'h0000_FFFC : 32'h0000_1000]}; \
      // higher range is not covered now due to limited generated codespace (amend if needed) \
    } \
    cp_lpend_``LOOP_IDX : coverpoint (csr_hwloop.lp_end[``LOOP_IDX``]) iff (csr_hwloop.lp_start_wb[``LOOP_IDX``] && csr_hwloop.lp_end_wb[``LOOP_IDX``] && csr_hwloop.lp_count_wb[``LOOP_IDX``]) { \
      bins lpend_range_0        = {[32'h0000_03FC : 32'h0000_0004]}; \
      bins lpend_range_1        = {[32'h0000_0FFC : 32'h0000_0400]}; \
      bins lpend_range_2        = {[32'h0000_FFFC : 32'h0000_1000]}; \
      // higher range is not covered now due to limited generated codespace (amend if needed) \
    } \
    cp_lpcount_``LOOP_IDX : coverpoint (csr_hwloop.lp_count[``LOOP_IDX``]) iff (csr_hwloop.lp_start_wb[``LOOP_IDX``] && csr_hwloop.lp_end_wb[``LOOP_IDX``] && csr_hwloop.lp_count_wb[``LOOP_IDX``]) { \
      // bins lpcount_zero           = {32'h0}; // valid CSR writes to sample should be when lpcount{0/1}.value != 0 \
      bins lpcount_range_low_1    = {[32'h0000_0190 : 32'h0000_0001]}; // count 0-400 \
      bins lpcount_range_low_2    = {[32'h0000_03FF : 32'h0000_0191]}; // count 401-1023 \
      bins lpcount_range_low_3    = {[32'h0000_0FFE : 32'h0000_0400]}; // count 1024-4094 \
      bins lpcount_range_low_4    = {32'h0000_0FFF}; // 4095 \
      // higher counts are not covered now to reduced simtime (amend if needed) \
    } \
    ccp_lpstart_0_lpend_lpcount_``LOOP_IDX : cross cp_lpstart_``LOOP_IDX``, cp_lpend_``LOOP_IDX``, cp_lpcount_``LOOP_IDX`` { \
      ignore_bins ignore__lpstart_range_1 = binsof (cp_lpstart_``LOOP_IDX``.lpstart_range_1); \
      ignore_bins ignore__lpstart_range_2 = binsof (cp_lpstart_``LOOP_IDX``.lpstart_range_2); \
      // ignore below due to long simtime if cross higher count with large loop \
      ignore_bins ignore__lpcount_low4    = binsof (cp_lpcount_``LOOP_IDX``.lpcount_range_low_4); \
    } \
    ccp_lpstart_1_lpend_lpcount_``LOOP_IDX : cross cp_lpstart_``LOOP_IDX``, cp_lpend_``LOOP_IDX``, cp_lpcount_``LOOP_IDX`` { \
      ignore_bins ignore__lpstart_range_0 = binsof (cp_lpstart_``LOOP_IDX``.lpstart_range_0); \
      ignore_bins ignore__lpstart_range_2 = binsof (cp_lpstart_``LOOP_IDX``.lpstart_range_2); \
      ignore_bins ignore__lpend_range_0   = binsof (cp_lpend_``LOOP_IDX``.lpend_range_0); \
      // ignore below due to long simtime if cross higher count with large loop \
      ignore_bins ignore__lpcount_low4    = binsof (cp_lpcount_``LOOP_IDX``.lpcount_range_low_4); \
    } \
    ccp_lpstart_2_lpend_lpcount_``LOOP_IDX : cross cp_lpstart_``LOOP_IDX``, cp_lpend_``LOOP_IDX``, cp_lpcount_``LOOP_IDX`` { \
      ignore_bins ignore__lpstart_range_0 = binsof (cp_lpstart_``LOOP_IDX``.lpstart_range_0); \
      ignore_bins ignore__lpstart_range_1 = binsof (cp_lpstart_``LOOP_IDX``.lpstart_range_1); \
      ignore_bins ignore__lpend_range_0   = binsof (cp_lpend_``LOOP_IDX``.lpend_range_0); \
      ignore_bins ignore__lpend_range_1   = binsof (cp_lpend_``LOOP_IDX``.lpend_range_1); \
      // ignore below due to long simtime if cross higher count with large loop \
      ignore_bins ignore__lpcount_low4    = binsof (cp_lpcount_``LOOP_IDX``.lpcount_range_low_4); \
    } \
  endgroup : cg_csr_hwloop_``LOOP_IDX

  `define CG_FEATURES_OF_HWLOOP(LOOP_IDX) cg_features_of_hwloop_``LOOP_IDX``
  `define DEF_CG_FEATURES_OF_HWLOOP(LOOP_IDX) covergroup cg_features_of_hwloop_``LOOP_IDX with function \
    sample(int lp_idx, s_hwloop_stat hwloop_stat, s_hwloop_cov hwloop_cov, bit [31:0] insn=32'b0, bit [31:0] irq=32'b0, hwloop_evt_loc_t evt_loc=TOTAL_LOC); \
    option.per_instance         = 1; \
    `ifdef MODEL_TECH \
    option.get_inst_coverage    = 1; \
    `endif \
    type_option.merge_instances = 1; \
    cp_hwloop_type : coverpoint (hwloop_stat.hwloop_type) iff (hwloop_stat.execute_instr_in_hwloop[``LOOP_IDX``]) { \
      bins single_hwloop      = {SINGLE}; \
      bins nested_hwloop      = {NESTED}; \
      illegal_bins invalid    = default; \
    } \
    cp_hwloop_setup : coverpoint (hwloop_stat.hwloop_setup[``LOOP_IDX``]) iff (hwloop_stat.execute_instr_in_hwloop[``LOOP_IDX``]) { \
      bins short_hwloop_setup = {SHORT}; \
      bins long_hwloop_setup  = {LONG}; \
      illegal_bins invalid    = default; \
    } \
    cp_hwloop_irq : coverpoint (irq) iff (hwloop_stat.execute_instr_in_hwloop[``LOOP_IDX``] && hwloop_cov.en_cov_irq) { \
      // priority order (high->low) : irq[31]...irq[16], irq[11], irq[3], irq[7] \
      bins vec_irq_1hot_priority[]    = {32'h0000_0008, \
                                         32'h0000_0080, \
                                         32'h0000_0800, \
                                         32'h0001_0000, 32'h0002_0000, 32'h0004_0000, 32'h0008_0000, \
                                         32'h0010_0000, 32'h0020_0000, 32'h0040_0000, 32'h0080_0000, \
                                         32'h0100_0000, 32'h0200_0000, 32'h0400_0000, 32'h0800_0000, \
                                         32'h1000_0000, 32'h2000_0000, 32'h4000_0000, 32'h8000_0000}; \
    } \
    cp_hwloop_dbg_haltreq : coverpoint (hwloop_stat.dbg_haltreq_cnt[lp_idx]) iff (hwloop_stat.execute_instr_in_hwloop[``LOOP_IDX``] && hwloop_cov.en_cov_dbg_haltreq) { \
      bins        dbg_haltreq     = {[1:$]}; \
    } \
    cp_hwloop_dbg_ebreakm : coverpoint (hwloop_stat.dbg_ebreakm_cnt[lp_idx]) iff (hwloop_stat.execute_instr_in_hwloop[``LOOP_IDX``] && hwloop_cov.en_cov_dbg_ebreakm) { \
      bins        dbg_ebreakm     = {[1:$]}; \
    } \
    cp_hwloop_dbg_trigger : coverpoint (hwloop_stat.dbg_trigger_cnt[lp_idx]) iff (hwloop_stat.execute_instr_in_hwloop[``LOOP_IDX``] && hwloop_cov.en_cov_dbg_trigger) { \
      bins        dbg_trigger     = {[1:$]}; \
    } \
    cp_hwloop_dbg_step_cnt : coverpoint (hwloop_stat.dbg_step_cnt[lp_idx]) iff (hwloop_stat.execute_instr_in_hwloop[``LOOP_IDX``] && hwloop_cov.en_cov_dbg_step_cnt) { \
      bins dbg_step_range_1       = {[1:4]}; \
      bins dbg_step_range_2       = {[5:20]}; \
      bins dbg_step_range_3       = {[20:50]}; \
      bins dbg_step_range_4       = {[51:$]}; \
    } \
    cp_hwloop_dbg_step_cnt_loc : coverpoint (hwloop_stat.dbg_step_cnt[lp_idx]) iff (hwloop_stat.execute_instr_in_hwloop[``LOOP_IDX``] && hwloop_cov.en_cov_dbg_step_cnt_loc) { \
      bins dbg_step_cnt_loc       = {[1:$]}; \
    } \
    cp_hwloop_excp_ebreak : coverpoint (hwloop_stat.excp_ebreak_cnt[lp_idx]) iff (hwloop_stat.execute_instr_in_hwloop[``LOOP_IDX``] && hwloop_cov.en_cov_excp_ebreak) { \
      bins        excp_ebreak     = {[1:$]}; \
    } \
    cp_hwloop_excp_ecall : coverpoint (hwloop_stat.excp_ecall_cnt[lp_idx]) iff (hwloop_stat.execute_instr_in_hwloop[``LOOP_IDX``] && hwloop_cov.en_cov_excp_ecall) { \
      bins        excp_ecall      = {[1:$]}; \
    } \
    cp_hwloop_excp_illegal : coverpoint (hwloop_stat.excp_illegal_cnt[lp_idx]) iff (hwloop_stat.execute_instr_in_hwloop[``LOOP_IDX``] && hwloop_cov.en_cov_excp_illegal) { \
      bins        excp_illegal    = {[1:$]}; \
    } \
    cp_hwloop_mc_insn : coverpoint (insn) iff (hwloop_stat.execute_instr_in_hwloop[``LOOP_IDX``] && hwloop_cov.en_cov_mc_insn) { \
      // RV32F \
      `RV32F_INSTR_BINS \
      // RV32M \
      wildcard bins div     = {TB_INSTR_DIV}; \
      wildcard bins divu    = {TB_INSTR_DIVU}; \
      wildcard bins rem     = {TB_INSTR_REM}; \
      wildcard bins remu    = {TB_INSTR_REMU}; \
      wildcard bins pmuh    = {TB_INSTR_PMUH}; \
      wildcard bins pmulhsu = {TB_INSTR_PMULHSU}; \
      wildcard bins pmulhu  = {TB_INSTR_PMULHU}; \
    } \
    cp_hwloop_loc : coverpoint (evt_loc) iff (hwloop_stat.execute_instr_in_hwloop[``LOOP_IDX``] && hwloop_cov.en_cov_event_loc) { \
      bins loc_lpstart        = {LOC_LPSTART}; \
      bins loc_lpstart_plus4  = {LOC_LPSTART_P4}; \
      bins loc_lpend          = {LOC_LPEND}; \
      bins loc_lpend_minus4   = {LOC_LPEND_M4}; \
      bins loc_others         = {LOC_OTHERS}; \
    } \
    // note: hwloop setup custom instructions are not allow in hwloop_0 (manual exclusion needed) \
    cp_insn_list_in_hwloop : coverpoint (insn) iff (hwloop_stat.execute_instr_in_hwloop[``LOOP_IDX``] && hwloop_cov.en_cov_insn) { \
      wildcard bins lui     = {TB_INSTR_LUI}; \
      wildcard bins auipc   = {TB_INSTR_AUIPC}; \
      // OPIMM \
      `OPIMM_INSTR_BINS \
      // OP \
      `OP_INSTR_BINS \
      // SYSTEM \
      wildcard bins csrrw   = {TB_INSTR_CSRRW}; \
      wildcard bins csrrs   = {TB_INSTR_CSRRS}; \
      wildcard bins csrrc   = {TB_INSTR_CSRRC}; \
      wildcard bins csrrwi  = {TB_INSTR_CSRRWI}; \
      wildcard bins csrrsi  = {TB_INSTR_CSRRSI}; \
      wildcard bins csrrci  = {TB_INSTR_CSRRCI}; \
      wildcard bins ecall   = {TB_INSTR_ECALL}; \
      wildcard bins ebreak  = {TB_INSTR_EBREAK}; \
      // RV32M \
      `RV32M_INSTR_BINS \
      // RV32F \
      `RV32F_INSTR_BINS \
      // LOAD STORE \
      `LOAD_STORE_INSTR_BINS \
      // RV32X \
      `RV32X_PULP_INSTR_BINS \
      // user-defined instructions \
      wildcard bins instr_illegal_exception = {{INSN_ILLEGAL}}; \
      wildcard bins instr_ebreakm           = {{INSN_EBREAKM}}; \
      // Others \
      illegal_bins other_instr              = default; \
    } \
    ccp_hwloop_type_setup_insn_list   : cross cp_hwloop_type, cp_hwloop_setup, cp_insn_list_in_hwloop; \
    ccp_hwloop_type_irq_loc           : cross cp_hwloop_type, cp_hwloop_loc, cp_hwloop_irq; \
    ccp_hwloop_type_dbg_haltreq_loc   : cross cp_hwloop_type, cp_hwloop_loc, cp_hwloop_dbg_haltreq; \
    ccp_hwloop_type_dbg_ebreakm_loc   : cross cp_hwloop_type, cp_hwloop_loc, cp_hwloop_dbg_ebreakm; \
    ccp_hwloop_type_dbg_trigger_loc   : cross cp_hwloop_type, cp_hwloop_loc, cp_hwloop_dbg_trigger; \
    ccp_hwloop_type_dbg_step_cnt      : cross cp_hwloop_type, cp_hwloop_dbg_step_cnt; /* todo: x with lpcount */ \
    ccp_hwloop_type_dbg_step_cnt_loc  : cross cp_hwloop_type, cp_hwloop_loc, cp_hwloop_dbg_step_cnt_loc; \
    ccp_hwloop_type_excp_ebreak_loc   : cross cp_hwloop_type, cp_hwloop_loc, cp_hwloop_excp_ebreak; \
    ccp_hwloop_type_excp_ecall_loc    : cross cp_hwloop_type, cp_hwloop_loc, cp_hwloop_excp_ecall; \
    ccp_hwloop_type_excp_illegal_loc  : cross cp_hwloop_type, cp_hwloop_loc, cp_hwloop_excp_illegal; \
    ccp_hwloop_type_excp_mc_insn_loc  : cross cp_hwloop_type, cp_hwloop_loc, cp_hwloop_mc_insn; \
  endgroup : cg_features_of_hwloop_``LOOP_IDX``

  `DEF_CG_CSR_HWLOOP(0)
  `DEF_CG_CSR_HWLOOP(1)
  `DEF_CG_FEATURES_OF_HWLOOP(0)
  `DEF_CG_FEATURES_OF_HWLOOP(1)

  // COVERGROUPS DEFINE HERE - START

  `uvm_component_utils(uvme_rv32x_hwloop_covg)

  function new(string name="uvme_rv32x_hwloop_covg", uvm_component parent=null);
    super.new(name, parent);
    `CG_CSR_HWLOOP(0)         = new(); `CG_CSR_HWLOOP(0).set_inst_name($sformatf("cg_csr_hwloop_0"));
    `CG_CSR_HWLOOP(1)         = new(); `CG_CSR_HWLOOP(1).set_inst_name($sformatf("cg_csr_hwloop_1"));
    `CG_FEATURES_OF_HWLOOP(0) = new(); `CG_FEATURES_OF_HWLOOP(0).set_inst_name($sformatf("cg_features_of_hwloop_0"));
    `CG_FEATURES_OF_HWLOOP(1) = new(); `CG_FEATURES_OF_HWLOOP(1).set_inst_name($sformatf("cg_features_of_hwloop_1"));
  endfunction: new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!(uvm_config_db#(virtual uvmt_cv32e40p_rvvi_if)::get(this, "", "cv32e40p_rvvi_vif", cv32e40p_rvvi_vif))) begin
        `uvm_fatal(_header, "cv32e40p_rvvi_vif no found in uvm_config_db");
    end
    if ($test$plusargs("skip_sampling_uvme_rv32x_hwloop_covg")) begin
      `uvm_info(_header, "Skip uvme_rv32x_hwloop_covg cvg sampling due to test intention", UVM_WARNING);
      en_cvg_sampling = 0;
    end
  endfunction : build_phase


  // conditions to collect location for different locations
  `define CHECK_PC_EQUAL_LPSTART(IN1, IN2, IN3, IN4)  is_pc_equal_lpstart(``IN1, ``IN2, ``IN3, ``IN4)
  `define CHECK_PC_EQUAL_LPEND(IN1, IN2, IN3, IN4)    is_pc_equal_lpend(``IN1, ``IN2, ``IN3, ``IN4)
  `define CHECK_PC_WITHIN_LP(IN1, IN2, IN3)           is_pc_within_lp(``IN1, ``IN2, ``IN3)
  `define IF_CURRENT_IS_MAIN_HWLOOP(LOOP_IDX, EVT) \
  if (``LOOP_IDX`` == 0 || ``LOOP_IDX`` == 1) begin \
    bit temp_in_nested_loop0 = (``LOOP_IDX`` == 0) ? 0 : in_nested_loop0; \
    if (hwloop_stat_main.execute_instr_in_hwloop[``LOOP_IDX``] && hwloop_stat_main.track_lp_cnt[``LOOP_IDX``] >= 0 && !temp_in_nested_loop0) begin \
      unique case (``EVT``) \
        EXCP_EBREAK: begin \
          hwloop_stat_main.excp_ebreak_cnt[``LOOP_IDX``]++; \
          if      (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][EXCP_EBREAK].push_back(LOC_LPSTART); \
          else if (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][EXCP_EBREAK].push_back(LOC_LPSTART_P4); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][EXCP_EBREAK].push_back(LOC_LPEND); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][EXCP_EBREAK].push_back(LOC_LPEND_M4); \
          else                                                                                                        hwloop_evt_loc_main[``LOOP_IDX``][EXCP_EBREAK].push_back(LOC_OTHERS); \
        end \
        EXCP_ECALL : begin \
          hwloop_stat_main.excp_ecall_cnt[``LOOP_IDX``]++; \
          if      (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][EXCP_ECALL].push_back(LOC_LPSTART); \
          else if (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][EXCP_ECALL].push_back(LOC_LPSTART_P4); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][EXCP_ECALL].push_back(LOC_LPEND); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][EXCP_ECALL].push_back(LOC_LPEND_M4); \
          else                                                                                                        hwloop_evt_loc_main[``LOOP_IDX``][EXCP_ECALL].push_back(LOC_OTHERS); \
        end \
        EXCP_ILLEGAL : begin \
          hwloop_stat_main.excp_illegal_cnt[``LOOP_IDX``]++; \
          if      (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][EXCP_ILLEGAL].push_back(LOC_LPSTART); \
          else if (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][EXCP_ILLEGAL].push_back(LOC_LPSTART_P4); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][EXCP_ILLEGAL].push_back(LOC_LPEND); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][EXCP_ILLEGAL].push_back(LOC_LPEND_M4); \
          else                                                                                                        hwloop_evt_loc_main[``LOOP_IDX``][EXCP_ILLEGAL].push_back(LOC_OTHERS); \
        end \
        IS_IRQ : begin \
          if      (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][IS_IRQ].push_back(LOC_LPSTART); \
          else if (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][IS_IRQ].push_back(LOC_LPSTART_P4); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][IS_IRQ].push_back(LOC_LPEND); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][IS_IRQ].push_back(LOC_LPEND_M4); \
          else                                                                                                        hwloop_evt_loc_main[``LOOP_IDX``][IS_IRQ].push_back(LOC_OTHERS); \
          irq_vect_main[``LOOP_IDX``].push_back(prev_irq_onehot_priority); \
        end \
        DBG_HALTREQ : begin \
          hwloop_stat_main.dbg_haltreq_cnt[``LOOP_IDX``]++; \
          if      (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][DBG_HALTREQ].push_back(LOC_LPSTART); \
          else if (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][DBG_HALTREQ].push_back(LOC_LPSTART_P4); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][DBG_HALTREQ].push_back(LOC_LPEND); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][DBG_HALTREQ].push_back(LOC_LPEND_M4); \
          else                                                                                                        hwloop_evt_loc_main[``LOOP_IDX``][DBG_HALTREQ].push_back(LOC_OTHERS); \
        end \
        DBG_TRIG : begin \
          hwloop_stat_main.dbg_trigger_cnt[``LOOP_IDX``]++; \
          if      (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][DBG_TRIG].push_back(LOC_LPSTART); \
          else if (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][DBG_TRIG].push_back(LOC_LPSTART_P4); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][DBG_TRIG].push_back(LOC_LPEND); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][DBG_TRIG].push_back(LOC_LPEND_M4); \
          else                                                                                                        hwloop_evt_loc_main[``LOOP_IDX``][DBG_TRIG].push_back(LOC_OTHERS); \
        end \
        DBG_STEP : begin \
          hwloop_stat_main.dbg_step_cnt[``LOOP_IDX``]++; \
          if      (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][DBG_STEP].push_back(LOC_LPSTART); \
          else if (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][DBG_STEP].push_back(LOC_LPSTART_P4); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][DBG_STEP].push_back(LOC_LPEND); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, prev_pc_rdata_main))         hwloop_evt_loc_main[``LOOP_IDX``][DBG_STEP].push_back(LOC_LPEND_M4); \
          else                                                                                                        hwloop_evt_loc_main[``LOOP_IDX``][DBG_STEP].push_back(LOC_OTHERS); \
        end \
        DBG_EBREAKM : begin \
          hwloop_stat_main.dbg_ebreakm_cnt[``LOOP_IDX``]++; \
          if      (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, cv32e40p_rvvi_vif.pc_rdata)) hwloop_evt_loc_main[``LOOP_IDX``][DBG_EBREAKM].push_back(LOC_LPSTART); \
          else if (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, cv32e40p_rvvi_vif.pc_rdata)) hwloop_evt_loc_main[``LOOP_IDX``][DBG_EBREAKM].push_back(LOC_LPSTART_P4); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, cv32e40p_rvvi_vif.pc_rdata)) hwloop_evt_loc_main[``LOOP_IDX``][DBG_EBREAKM].push_back(LOC_LPEND); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, cv32e40p_rvvi_vif.pc_rdata)) hwloop_evt_loc_main[``LOOP_IDX``][DBG_EBREAKM].push_back(LOC_LPEND_M4); \
          else                                                                                                        hwloop_evt_loc_main[``LOOP_IDX``][DBG_EBREAKM].push_back(LOC_OTHERS); \
        end \
        MC_INSN : begin \
          if      (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, cv32e40p_rvvi_vif.pc_rdata)) hwloop_evt_loc_main[``LOOP_IDX``][MC_INSN].push_back(LOC_LPSTART); \
          else if (`CHECK_PC_EQUAL_LPSTART(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, cv32e40p_rvvi_vif.pc_rdata)) hwloop_evt_loc_main[``LOOP_IDX``][MC_INSN].push_back(LOC_LPSTART_P4); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 0, cv32e40p_rvvi_vif.pc_rdata)) hwloop_evt_loc_main[``LOOP_IDX``][MC_INSN].push_back(LOC_LPEND); \
          else if (  `CHECK_PC_EQUAL_LPEND(hwloop_stat_main.hwloop_csr, ``LOOP_IDX``, 1, cv32e40p_rvvi_vif.pc_rdata)) hwloop_evt_loc_main[``LOOP_IDX``][MC_INSN].push_back(LOC_LPEND_M4); \
          else                                                                                                        hwloop_evt_loc_main[``LOOP_IDX``][MC_INSN].push_back(LOC_OTHERS); \
        end \
      endcase  \
    end \
  end

  // task to sample cg_csr_hwloop
  `define CHECK_N_SAMPLE_CSR_HWLOOP(TYPE) check_n_sample_csr_hwloop_``TYPE``();
  `define DEF_CHECK_N_SAMPLE_CSR_HWLOOP(TYPE) task check_n_sample_csr_hwloop_``TYPE``(); \
    for (int i=0; i<HWLOOP_NB; i++) begin \
      int short_setup_cnt = 0; // use for cv.setup (all start, end and count happen stimultenously in one cycle) \
      if (cv32e40p_rvvi_vif.csr_wb[CSR_LPSTART0_ADDR+i*4]) begin : UPDATE_LPSTART \
        csr_hwloop_``TYPE``.lp_start[i]    = cv32e40p_rvvi_vif.csr[CSR_LPSTART0_ADDR+i*4]; \
        csr_hwloop_``TYPE``.lp_start_wb[i] = cv32e40p_rvvi_vif.csr_wb[CSR_LPSTART0_ADDR+i*4]; \
        short_setup_cnt++; \
      end \
      if (cv32e40p_rvvi_vif.csr_wb[CSR_LPEND0_ADDR+i*4]) begin : UPDATE_LPEND \
        csr_hwloop_``TYPE``.lp_end[i]      = cv32e40p_rvvi_vif.csr[CSR_LPEND0_ADDR+i*4]; \
        csr_hwloop_``TYPE``.lp_end_wb[i]   = cv32e40p_rvvi_vif.csr_wb[CSR_LPEND0_ADDR+i*4]; \
        short_setup_cnt++; \
      end \
      if (cv32e40p_rvvi_vif.csr_wb[CSR_LPCOUNT0_ADDR+i*4]) begin : UPDATE_LPCOUNT \
        csr_hwloop_``TYPE``.lp_count[i]    = cv32e40p_rvvi_vif.csr[CSR_LPCOUNT0_ADDR+i*4]; \
        csr_hwloop_``TYPE``.lp_count_wb[i] = cv32e40p_rvvi_vif.csr_wb[CSR_LPCOUNT0_ADDR+i*4]; \
        short_setup_cnt++; \
      end \
      if (csr_hwloop_``TYPE``.lp_start_wb[i] && csr_hwloop_``TYPE``.lp_end_wb[i] && csr_hwloop_``TYPE``.lp_count_wb[i]) begin : SAMPLE_HWLOP_CSR \
        if (csr_hwloop_``TYPE``.lp_count[i] != 0 && !hwloop_stat_``TYPE``.sample_hwloop_csr_done[i]) begin \
            `uvm_info(_header, $sformatf("DEBUG - cg_csr_hwloop[%0d] - sampling csr_hwloop is %p", i, csr_hwloop_``TYPE``), UVM_DEBUG); \
            unique case (i) \
              0:  begin \
                    `CG_CSR_HWLOOP(0).sample(csr_hwloop_``TYPE``); \
                    `uvm_info(_header, $sformatf("DEBUG - cg_csr_hwloop[%0d] - get_inst_coverage = %.2f, get_coverage = %.2f", i, `CG_CSR_HWLOOP(0).get_inst_coverage(), `CG_CSR_HWLOOP(0).get_coverage), UVM_DEBUG); \
                  end \
              1:  begin \
                    `CG_CSR_HWLOOP(1).sample(csr_hwloop_``TYPE``); \
                    `uvm_info(_header, $sformatf("DEBUG - cg_csr_hwloop[%0d] - get_inst_coverage = %.2f, get_coverage = %.2f", i, `CG_CSR_HWLOOP(1).get_inst_coverage(), `CG_CSR_HWLOOP(1).get_coverage), UVM_DEBUG); \
                  end \
            endcase \
          // update hwloop_stat \
          hwloop_stat_``TYPE``.hwloop_csr.lp_start[i] = csr_hwloop_``TYPE``.lp_start[i]; \
          hwloop_stat_``TYPE``.hwloop_csr.lp_end[i]   = csr_hwloop_``TYPE``.lp_end[i]; \
          hwloop_stat_``TYPE``.hwloop_csr.lp_count[i] = csr_hwloop_``TYPE``.lp_count[i]; \
          if (short_setup_cnt == 3) \
            hwloop_stat_``TYPE``.hwloop_setup[i]      = SHORT; \
          else                       \
            hwloop_stat_``TYPE``.hwloop_setup[i]      = LONG; \
          hwloop_stat_``TYPE``.sample_hwloop_csr_done[i] = 1'b1; \
        end \
        else if (hwloop_stat_``TYPE``.execute_instr_in_hwloop[i]) begin \
          hwloop_stat_``TYPE``.hwloop_csr.lp_start[i] = csr_hwloop_``TYPE``.lp_start[i]; \
          hwloop_stat_``TYPE``.hwloop_csr.lp_end[i]   = csr_hwloop_``TYPE``.lp_end[i]; \
          hwloop_stat_``TYPE``.hwloop_csr.lp_count[i] = csr_hwloop_``TYPE``.lp_count[i]; \
        end \
      end // SAMPLE_HWLOP_CSR \
    end // for \
  endtask : check_n_sample_csr_hwloop_``TYPE``

  `DEF_CHECK_N_SAMPLE_CSR_HWLOOP(main)
  // `DEF_CHECK_N_SAMPLE_CSR_HWLOOP(sub)

  // task to sample cg_features_of_hwloop
  `define MC_INSN_OP_CODE  {OPCODE_OP, OPCODE_OP_FP, OPCODE_OP_FMADD, OPCODE_OP_FNMADD, OPCODE_OP_FMSUB, OPCODE_OP_FNMSUB, OPCODE_LOAD_FP, OPCODE_STORE_FP}
  `define CHECK_N_SAMPLE_HWLOOP(TYPE) check_n_sample_hwloop_``TYPE``();
  `define DEF_CHECK_N_SAMPLE_HWLOOP(TYPE) task check_n_sample_hwloop_``TYPE``(); \
    for (int i=0; i<HWLOOP_NB; i++) begin : UPDATE_HWLOOP_STAT \
      if (hwloop_stat_``TYPE``.hwloop_csr.lp_count[i] != 0) begin \
        if (is_pc_equal_lpstart(hwloop_stat_``TYPE``.hwloop_csr, i, 0, cv32e40p_rvvi_vif.pc_rdata) && hwloop_stat_``TYPE``.track_lp_cnt[i] == 0) begin \
          hwloop_stat_``TYPE``.execute_instr_in_hwloop[i] = 1'b1; \
          hwloop_stat_``TYPE``.track_lp_cnt[i]          = hwloop_stat_``TYPE``.hwloop_csr.lp_count[i]; \
          if      ( hwloop_stat_``TYPE``.execute_instr_in_hwloop[0] &&  hwloop_stat_``TYPE``.execute_instr_in_hwloop[1]) hwloop_stat_``TYPE``.hwloop_type = NESTED; \
          else if ( hwloop_stat_``TYPE``.execute_instr_in_hwloop[0] && !hwloop_stat_``TYPE``.execute_instr_in_hwloop[1]) hwloop_stat_``TYPE``.hwloop_type = SINGLE; \
          else if (!hwloop_stat_``TYPE``.execute_instr_in_hwloop[0] &&  hwloop_stat_``TYPE``.execute_instr_in_hwloop[1]) hwloop_stat_``TYPE``.hwloop_type = SINGLE; \
        end \
      end \
    end // UPDATE_HWLOOP_STAT \
    for (int i=0; i<HWLOOP_NB; i++) begin : COLLECT_INSTR \
      if (hwloop_stat_``TYPE``.execute_instr_in_hwloop[i]) begin \
        lpend_has_pending_irq_``TYPE``[i] = 0; \
        done_insn_list_capture_d1_``TYPE``[i] = done_insn_list_capture_``TYPE``[i]; \
        unique case (i) \
          0 : begin // nested or single is the same \
                if (!done_insn_list_capture_``TYPE``[i]) begin \
                  if (is_illegal)       insn_list_in_hwloop_``TYPE``[i].push_back(INSN_ILLEGAL); \
                  else if (is_ebreakm)  insn_list_in_hwloop_``TYPE``[i].push_back(INSN_EBREAKM); \
                  else                  insn_list_in_hwloop_``TYPE``[i].push_back(cv32e40p_rvvi_vif.insn); \
                  if (cv32e40p_rvvi_vif.insn[6:0] inside `MC_INSN_OP_CODE) begin \
                    if ((cv32e40p_rvvi_vif.insn[6:0] == OPCODE_OP && cv32e40p_rvvi_vif.insn[31:25] != 7'b0000001) || \
                        (cv32e40p_rvvi_vif.insn[6:0] == OPCODE_OP && cv32e40p_rvvi_vif.insn[14:12] == 3'b000) \
                    ) is_mc_insn = 0; \
                    else begin \
                      is_mc_insn = 1;  mc_insn_list_in_hwloop_``TYPE``[i].push_back(cv32e40p_rvvi_vif.insn); \
                      `IF_CURRENT_IS_MAIN_HWLOOP(i, MC_INSN) \
                    end \
                  end \
                  else is_mc_insn = 0; \
                  check_ebreakm_entry(i); \
                end \
                else if (is_ebreakm) begin \
                  insn_list_in_hwloop_``TYPE``[i].push_back(INSN_EBREAKM); \
                  check_ebreakm_entry(i); \
                end \
                if (is_pc_equal_lpend(hwloop_stat_``TYPE``.hwloop_csr, i, 0, cv32e40p_rvvi_vif.pc_rdata) && hwloop_stat_``TYPE``.track_lp_cnt[i] != 0) begin \
                  if (pending_irq_ack && cv32e40p_rvvi_vif.trap) lpend_has_pending_irq_``TYPE``[i] = 1; \
                  hwloop_stat_``TYPE``.track_lp_cnt[i]--; \
                  done_insn_list_capture_``TYPE``[i] = 1; \
                  assert(hwloop_stat_``TYPE``.track_lp_cnt[i] >= 0); \
                end \
              end \
          1 : begin // in nested, skip when executing hwloop0  \
                in_nested_loop0_d1 = in_nested_loop0; \
                if (hwloop_stat_``TYPE``.hwloop_type == NESTED && hwloop_stat_``TYPE``.track_lp_cnt[0] != 0) begin \
                  in_nested_loop0 = 1; continue; \
                end \
                else if (hwloop_stat_``TYPE``.hwloop_type == NESTED && hwloop_stat_``TYPE``.track_lp_cnt[0] == 0 && in_nested_loop0) begin \
                  in_nested_loop0 = 0; continue; \
                end \
                if (!done_insn_list_capture_``TYPE``[i]) begin \
                  if (is_illegal)       insn_list_in_hwloop_``TYPE``[i].push_back(INSN_ILLEGAL); \
                  else if (is_ebreakm)  insn_list_in_hwloop_``TYPE``[i].push_back(INSN_EBREAKM); \
                  else                  insn_list_in_hwloop_``TYPE``[i].push_back(cv32e40p_rvvi_vif.insn); \
                  if (cv32e40p_rvvi_vif.insn[6:0] inside `MC_INSN_OP_CODE) begin \
                    if ((cv32e40p_rvvi_vif.insn[6:0] == OPCODE_OP && cv32e40p_rvvi_vif.insn[31:25] != 7'b0000001) || \
                        (cv32e40p_rvvi_vif.insn[6:0] == OPCODE_OP && cv32e40p_rvvi_vif.insn[14:12] == 3'b000) \
                    ) is_mc_insn = 0; \
                    else begin \
                      is_mc_insn = 1;  mc_insn_list_in_hwloop_``TYPE``[i].push_back(cv32e40p_rvvi_vif.insn); \
                      `IF_CURRENT_IS_MAIN_HWLOOP(i, MC_INSN) \
                    end \
                  end \
                  else is_mc_insn = 0; \
                  check_ebreakm_entry(i); \
                end \
                else if (is_ebreakm) begin \
                  insn_list_in_hwloop_``TYPE``[i].push_back(INSN_EBREAKM); \
                  check_ebreakm_entry(i); \
                end \
                if (is_pc_equal_lpend(hwloop_stat_``TYPE``.hwloop_csr, i, 0, cv32e40p_rvvi_vif.pc_rdata) && hwloop_stat_``TYPE``.track_lp_cnt[i] != 0) begin \
                  if (pending_irq_ack && cv32e40p_rvvi_vif.trap) lpend_has_pending_irq_``TYPE``[i] = 1; \
                  hwloop_stat_``TYPE``.track_lp_cnt[i]--; \
                  done_insn_list_capture_``TYPE``[i] = 1; \
                  assert(hwloop_stat_``TYPE``.track_lp_cnt[i] >= 0); \
                end \
              end \
        endcase  \
      end \
    end // COLLECT_INSTR \
    if ( \
      (hwloop_stat_``TYPE``.hwloop_type == NESTED && done_insn_list_capture_``TYPE``[1] && hwloop_stat_``TYPE``.track_lp_cnt[1] == 0) || \
      (hwloop_stat_``TYPE``.hwloop_type == SINGLE && done_insn_list_capture_``TYPE``[1] && hwloop_stat_``TYPE``.track_lp_cnt[1] == 0) || \
      (hwloop_stat_``TYPE``.hwloop_type == SINGLE && done_insn_list_capture_``TYPE``[0] && hwloop_stat_``TYPE``.track_lp_cnt[0] == 0) \
    ) begin : SAMPLE_END_OF_HWLOOPS \
      for (int i=0; i<HWLOOP_NB; i++) begin \
        // FOR_CP_INSN_LIST_IN_HWLOOP \
        hwloop_cov_``TYPE``[i].en_cov_insn = 1; \
        while (insn_list_in_hwloop_``TYPE``[i].size() != 0) begin \
          bit [31:0] insn_item; \
          insn_item = insn_list_in_hwloop_``TYPE``[i].pop_front(); \
          `uvm_info(_header, $sformatf("DEBUG - FOR_CP_INSN_LIST_IN_HWLOOP - LOOP_%0d - insn_item is %8h", i, insn_item), UVM_DEBUG); \
          unique case (i) \
            0:  begin \
                  `CG_FEATURES_OF_HWLOOP(0).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .insn(insn_item)); \
                end \
            1:  begin  \
                  `CG_FEATURES_OF_HWLOOP(1).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .insn(insn_item)); \
                end \
          endcase \
        end \
        hwloop_cov_``TYPE``[i].en_cov_insn = 0; \
        // FOR_CP_HWLOOP_IRQ_LOC \
        hwloop_cov_``TYPE``[i].en_cov_irq = 1; hwloop_cov_``TYPE``[i].en_cov_event_loc = 1; \
        while (irq_vect_``TYPE``[i].size() != 0) begin \
          bit [31:0]    irq_item; \
          hwloop_evt_loc_t  evt_loc; \
          irq_item = irq_vect_``TYPE``[i].pop_front(); \
          evt_loc  = hwloop_evt_loc_``TYPE``[i][IS_IRQ].pop_front(); \
          `uvm_info(_header, $sformatf("DEBUG - FOR_CP_HWLOOP_IRQ_LOC - LOOP_%0d - irq_item is %8h at loc[%s]", i, irq_item, evt_loc.name()), UVM_DEBUG); \
          unique case (i) \
            0:  begin \
                  `CG_FEATURES_OF_HWLOOP(0).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .irq(irq_item), .evt_loc(evt_loc)); \
                end \
            1:  begin  \
                  `CG_FEATURES_OF_HWLOOP(1).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .irq(irq_item), .evt_loc(evt_loc)); \
                end \
          endcase \
        end \
        hwloop_evt_loc_``TYPE``[i][IS_IRQ].delete(); \
        hwloop_cov_``TYPE``[i].en_cov_irq = 0; \
        // FOR_CP_HWLOOP_DBG_HALTREQ \
        hwloop_cov_``TYPE``[i].en_cov_dbg_haltreq = 1; hwloop_cov_``TYPE``[i].en_cov_event_loc = 1; \
        for (int j=0; j<hwloop_stat_``TYPE``.dbg_haltreq_cnt[i]; j++) begin \
          hwloop_evt_loc_t  evt_loc; \
          evt_loc  = hwloop_evt_loc_``TYPE``[i][DBG_HALTREQ].pop_front(); \
          `uvm_info(_header, $sformatf("DEBUG - FOR_CP_HWLOOP_DBG_HALTREQ - LOOP_%0d - dbg_haltreq at loc[%s]", i, evt_loc.name()), UVM_DEBUG); \
          unique case (i) \
            0:  begin \
                  `CG_FEATURES_OF_HWLOOP(0).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .evt_loc(evt_loc)); \
                end \
            1:  begin  \
                  `CG_FEATURES_OF_HWLOOP(1).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .evt_loc(evt_loc)); \
                end \
          endcase \
        end \
        hwloop_evt_loc_``TYPE``[i][DBG_HALTREQ].delete(); \
        hwloop_cov_``TYPE``[i].en_cov_dbg_haltreq = 0; \
        // FOR_CP_HWLOOP_DBG_EBREAKM \
        hwloop_cov_``TYPE``[i].en_cov_dbg_ebreakm = 1; hwloop_cov_``TYPE``[i].en_cov_event_loc = 1; \
        for (int j=0; j<hwloop_stat_``TYPE``.dbg_ebreakm_cnt[i]; j++) begin \
          hwloop_evt_loc_t  evt_loc; \
          evt_loc  = hwloop_evt_loc_``TYPE``[i][DBG_EBREAKM].pop_front(); \
          `uvm_info(_header, $sformatf("DEBUG - FOR_CP_HWLOOP_DBG_EBREAKM - LOOP_%0d - dbg_ebreakm at loc[%s]", i, evt_loc.name()), UVM_DEBUG); \
          unique case (i) \
            0:  begin \
                  `CG_FEATURES_OF_HWLOOP(0).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .evt_loc(evt_loc)); \
                end \
            1:  begin  \
                  `CG_FEATURES_OF_HWLOOP(1).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .evt_loc(evt_loc)); \
                end \
          endcase \
        end \
        hwloop_evt_loc_``TYPE``[i][DBG_EBREAKM].delete(); \
        hwloop_cov_``TYPE``[i].en_cov_dbg_ebreakm = 0; \
        // FOR_CP_HWLOOP_DBG_TRIGGER \
        hwloop_cov_``TYPE``[i].en_cov_dbg_trigger = 1; hwloop_cov_``TYPE``[i].en_cov_event_loc = 1; \
        for (int j=0; j<hwloop_stat_``TYPE``.dbg_trigger_cnt[i]; j++) begin \
          hwloop_evt_loc_t  evt_loc; \
          evt_loc  = hwloop_evt_loc_``TYPE``[i][DBG_TRIG].pop_front(); \
          `uvm_info(_header, $sformatf("DEBUG - FOR_CP_HWLOOP_DBG_TRIGGER - LOOP_%0d - dbg_trigger at loc[%s]", i, evt_loc.name()), UVM_DEBUG); \
          unique case (i) \
            0:  begin \
                  `CG_FEATURES_OF_HWLOOP(0).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .evt_loc(evt_loc)); \
                end \
            1:  begin  \
                  `CG_FEATURES_OF_HWLOOP(1).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .evt_loc(evt_loc)); \
                end \
          endcase \
        end \
        hwloop_evt_loc_``TYPE``[i][DBG_TRIG].delete(); \
        hwloop_cov_``TYPE``[i].en_cov_dbg_trigger = 0; \
        // FOR_CP_HWLOOP_DBG_STEP_CNT \
        hwloop_cov_``TYPE``[i].en_cov_dbg_step_cnt = 1; hwloop_cov_``TYPE``[i].en_cov_event_loc = 0; \
        if (hwloop_stat_``TYPE``.dbg_step_cnt[i] > 0) begin \
          `uvm_info(_header, $sformatf("DEBUG - FOR_CP_HWLOOP_DBG_STEP_CNT - LOOP_%0d - dbg_step_cnt %0d", i, hwloop_stat_``TYPE``.dbg_step_cnt[i]), UVM_DEBUG); \
          unique case (i) \
            0:  begin \
                  `CG_FEATURES_OF_HWLOOP(0).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i])); \
                end \
            1:  begin  \
                  `CG_FEATURES_OF_HWLOOP(1).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i])); \
                end \
          endcase \
        end \
        hwloop_cov_``TYPE``[i].en_cov_dbg_step_cnt = 0; \
        // FOR_CP_HWLOOP_DBG_STEP_CNT_LOC \
        hwloop_cov_``TYPE``[i].en_cov_dbg_step_cnt_loc = 1; hwloop_cov_``TYPE``[i].en_cov_event_loc = 1; \
        for (int j=0; j<hwloop_stat_``TYPE``.dbg_step_cnt[i]; j++) begin \
          hwloop_evt_loc_t  evt_loc; \
          evt_loc  = hwloop_evt_loc_``TYPE``[i][DBG_STEP].pop_front(); \
          `uvm_info(_header, $sformatf("DEBUG - FOR_CP_HWLOOP_DBG_STEP_CNT_LOC - LOOP_%0d - dbg_step at loc[%s]", i, evt_loc.name()), UVM_DEBUG); \
          unique case (i) \
            0:  begin \
                  `CG_FEATURES_OF_HWLOOP(0).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .evt_loc(evt_loc)); \
                end \
            1:  begin  \
                  `CG_FEATURES_OF_HWLOOP(1).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .evt_loc(evt_loc)); \
                end \
          endcase \
        end \
        hwloop_evt_loc_``TYPE``[i][DBG_STEP].delete(); \
        hwloop_cov_``TYPE``[i].en_cov_dbg_step_cnt_loc = 0; \
        // FOR_CP_HWLOOP_EXCP_EBREAK \
        hwloop_cov_``TYPE``[i].en_cov_excp_ebreak = 1; hwloop_cov_``TYPE``[i].en_cov_event_loc = 1; \
        for (int j=0; j<hwloop_stat_``TYPE``.excp_ebreak_cnt[i]; j++) begin \
          hwloop_evt_loc_t  evt_loc; \
          evt_loc  = hwloop_evt_loc_``TYPE``[i][EXCP_EBREAK].pop_front(); \
          `uvm_info(_header, $sformatf("DEBUG - FOR_CP_HWLOOP_EXCP_EBREAK - LOOP_%0d - excp_ebreak at loc[%s]", i, evt_loc.name()), UVM_DEBUG); \
          unique case (i) \
            0:  begin \
                  `CG_FEATURES_OF_HWLOOP(0).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .evt_loc(evt_loc)); \
                end \
            1:  begin  \
                  `CG_FEATURES_OF_HWLOOP(1).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .evt_loc(evt_loc)); \
                end \
          endcase \
        end \
        hwloop_evt_loc_``TYPE``[i][EXCP_EBREAK].delete(); \
        hwloop_cov_``TYPE``[i].en_cov_excp_ebreak = 0; \
        // FOR_CP_HWLOOP_EXCP_ECALL \
        hwloop_cov_``TYPE``[i].en_cov_excp_ecall = 1; hwloop_cov_``TYPE``[i].en_cov_event_loc = 1; \
        for (int j=0; j<hwloop_stat_``TYPE``.excp_ecall_cnt[i]; j++) begin \
          hwloop_evt_loc_t  evt_loc; \
          evt_loc  = hwloop_evt_loc_``TYPE``[i][EXCP_ECALL].pop_front(); \
          `uvm_info(_header, $sformatf("DEBUG - FOR_CP_HWLOOP_EXCP_ECALL - LOOP_%0d - excp_ecall at loc[%s]", i, evt_loc.name()), UVM_DEBUG); \
          unique case (i) \
            0:  begin \
                  `CG_FEATURES_OF_HWLOOP(0).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .evt_loc(evt_loc)); \
                end \
            1:  begin  \
                  `CG_FEATURES_OF_HWLOOP(1).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .evt_loc(evt_loc)); \
                end \
          endcase \
        end \
        hwloop_evt_loc_``TYPE``[i][EXCP_ECALL].delete(); \
        hwloop_cov_``TYPE``[i].en_cov_excp_ecall = 0; \
        // FOR_CP_HWLOOP_EXCP_ILLEGAL \
        hwloop_cov_``TYPE``[i].en_cov_excp_illegal = 1; hwloop_cov_``TYPE``[i].en_cov_event_loc = 1; \
        for (int j=0; j<hwloop_stat_``TYPE``.excp_illegal_cnt[i]; j++) begin \
          hwloop_evt_loc_t  evt_loc; \
          evt_loc  = hwloop_evt_loc_``TYPE``[i][EXCP_ILLEGAL].pop_front(); \
          `uvm_info(_header, $sformatf("DEBUG - FOR_CP_HWLOOP_EXCP_ILLEGAL - LOOP_%0d - excp_illegal at loc[%s]", i, evt_loc.name()), UVM_DEBUG); \
          unique case (i) \
            0:  begin \
                  `CG_FEATURES_OF_HWLOOP(0).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .evt_loc(evt_loc)); \
                end \
            1:  begin  \
                  `CG_FEATURES_OF_HWLOOP(1).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .evt_loc(evt_loc)); \
                end \
          endcase \
        end \
        hwloop_evt_loc_``TYPE``[i][EXCP_ILLEGAL].delete(); \
        hwloop_cov_``TYPE``[i].en_cov_excp_illegal = 0; \
        // FOR_CP_HWLOOP_MC_INSN \
        hwloop_cov_``TYPE``[i].en_cov_mc_insn = 1; hwloop_cov_``TYPE``[i].en_cov_event_loc = 1; \
        while (mc_insn_list_in_hwloop_``TYPE``[i].size() != 0) begin \
          bit [31:0] insn_item; \
          hwloop_evt_loc_t  evt_loc; \
          insn_item = mc_insn_list_in_hwloop_``TYPE``[i].pop_front(); \
          evt_loc   = hwloop_evt_loc_``TYPE``[i][MC_INSN].pop_front(); \
          `uvm_info(_header, $sformatf("DEBUG - FOR_CP_HWLOOP_MC_INSN - LOOP_%0d - insn_item is %8h at loc[%s]", i, insn_item, evt_loc.name()), UVM_DEBUG); \
          unique case (i) \
            0:  begin \
                  `CG_FEATURES_OF_HWLOOP(0).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .insn(insn_item), .evt_loc(evt_loc)); \
                end \
            1:  begin  \
                  `CG_FEATURES_OF_HWLOOP(1).sample(.lp_idx(i), .hwloop_stat(hwloop_stat_``TYPE``), .hwloop_cov(hwloop_cov_``TYPE``[i]), .insn(insn_item), .evt_loc(evt_loc)); \
                end \
          endcase \
        end \
        hwloop_evt_loc_``TYPE``[i][MC_INSN].delete(); \
        hwloop_cov_``TYPE``[i].en_cov_mc_insn = 0; \
        lpend_has_pending_irq_``TYPE``[i]     = 0; \
        done_insn_list_capture_``TYPE``[i]    = 0; \
        done_insn_list_capture_d1_``TYPE``[i] = 0; \
        hwloop_cov_``TYPE``[i]                = hwloop_cov_init[i]; \
      end // for HWLOOP_NB \
      csr_hwloop_``TYPE``     = csr_hwloop_init; \
      hwloop_stat_``TYPE``    = hwloop_stat_init; \
      in_nested_loop0         = 0; \
      in_nested_loop0_d1      = 0; \
    end // SAMPLE_END_OF_HWLOOPS \
  endtask : check_n_sample_hwloop_``TYPE``

  `DEF_CHECK_N_SAMPLE_HWLOOP(main)
  // `DEF_CHECK_N_SAMPLE_HWLOOP(sub)


  function void check_exception_entry(int lp_idx);
      exception_code = exception_code_t'(cv32e40p_rvvi_vif.csr_mcause_ecp_code);
      case (exception_code)
        CODE_EBREAK :  begin
          if (lp_idx)  begin `IF_CURRENT_IS_MAIN_HWLOOP(1, EXCP_EBREAK) end
          else         begin `IF_CURRENT_IS_MAIN_HWLOOP(0, EXCP_EBREAK) end 
        end
        CODE_ECALL :   begin
          if (lp_idx)  begin `IF_CURRENT_IS_MAIN_HWLOOP(1, EXCP_ECALL) end
          else         begin `IF_CURRENT_IS_MAIN_HWLOOP(0, EXCP_ECALL) end 
        end
        CODE_ILLEGAL : begin
          if (lp_idx)  begin `IF_CURRENT_IS_MAIN_HWLOOP(1, EXCP_ILLEGAL) end
          else         begin `IF_CURRENT_IS_MAIN_HWLOOP(0, EXCP_ILLEGAL) end 
        end
        default: begin `uvm_error(_header, $sformatf("DEBUG - Invalid csr_mcause_ecp_code %5d", cv32e40p_rvvi_vif.csr_mcause_ecp_code)); end
      endcase
  endfunction : check_exception_entry

  function void check_ebreakm_entry(int lp_idx);
    if (cv32e40p_rvvi_vif.csr_dcsr_ebreakm && cv32e40p_rvvi_vif.insn == TB_INSTR_EBREAK) begin
      if (lp_idx) begin `IF_CURRENT_IS_MAIN_HWLOOP(1, DBG_EBREAKM) end
      else        begin `IF_CURRENT_IS_MAIN_HWLOOP(0, DBG_EBREAKM) end 
    end
  endfunction : check_ebreakm_entry

  function void check_exception_exit();
    if (cv32e40p_rvvi_vif.valid && cv32e40p_rvvi_vif.insn == TB_INSTR_MRET && !cv32e40p_rvvi_vif.trap) begin
      is_ebreak = 0; is_ecall = 0; is_illegal = 0; is_trap = 0;
      `uvm_info(_header, $sformatf("DEBUG - EXCEPTION Exit"), UVM_DEBUG);
    end
  endfunction : check_exception_exit

  function void update_prev_irq_onehot_priority();
    prev_irq_onehot_priority = cv32e40p_rvvi_vif.irq_onehot_priority;
  endfunction : update_prev_irq_onehot_priority

  function bit pc_is_mtvec_addr();
    if (cv32e40p_rvvi_vif.pc_rdata >= cv32e40p_rvvi_vif.mtvec_base_addr && cv32e40p_rvvi_vif.pc_rdata < (cv32e40p_rvvi_vif.mtvec_base_addr + 32*4)) return 1; // direct or vector mode
    else return 0;
  endfunction : pc_is_mtvec_addr

  function bit is_mcause_irq();
    return cv32e40p_rvvi_vif.csr_mcause_irq;
  endfunction : is_mcause_irq

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    wait(en_cvg_sampling);

    fork // Background threads - START

      forever begin : SET_EXCEPTION_FLAG
        wait (cv32e40p_rvvi_vif.clk && cv32e40p_rvvi_vif.valid && cv32e40p_rvvi_vif.trap);
        if (
          cv32e40p_rvvi_vif.csr_trig_execute && cv32e40p_rvvi_vif.csr_trig_pc == cv32e40p_rvvi_vif.pc_rdata // debug trig match assert trap
        ) begin
          is_trap = 0;
          wait (!cv32e40p_rvvi_vif.trap); // bypass and do nothing
          has_trap_due2_dbg_match_trig = 1;
        end
        else if ((cv32e40p_rvvi_vif.csr_dcsr_step || !pending_irq_ack) && !is_dbg_mode && !is_irq) begin // set excep flag only if no pending irq is serving, not in irq and not in dbg mode
          is_trap = 1;
          case (cv32e40p_rvvi_vif.insn)
            TB_INSTR_EBREAK, INSTR_CBREAK : if (cv32e40p_rvvi_vif.csr_dcsr_ebreakm) begin 
                                              is_trap = 0;
                                              @(posedge cv32e40p_rvvi_vif.clk); continue; 
                                            end 
                                            else begin is_ebreak  = 1; `uvm_info(_header, $sformatf("DEBUG - EXCEPTION Entry due to EBREAK"), UVM_DEBUG); end
            TB_INSTR_ECALL                : begin      is_ecall   = 1; `uvm_info(_header, $sformatf("DEBUG - EXCEPTION Entry due to ECALL"), UVM_DEBUG); end
            default                       : begin      is_illegal = 1; `uvm_info(_header, $sformatf("DEBUG - EXCEPTION Entry due to ILLEGAL"), UVM_DEBUG); end
          endcase
          wait (!(is_ebreak | is_ecall | is_illegal));
        end
        else begin 
          is_trap = 0;
          wait (!cv32e40p_rvvi_vif.trap); 
        end // bypass if pending irq exist
      end // EXCEPTION_HANDLING

      forever begin : UPDATE_PREV_IRQ_ONEHOT_PRIORITY_IS_0
        @(posedge cv32e40p_rvvi_vif.clk);
        if (prev_irq_onehot_priority == 0) prev_irq_onehot_priority_is_0 = 1;
        else                               prev_irq_onehot_priority_is_0 = 0;
      end
      forever begin : SET_PENDING_IRQ_ACK
        @(cv32e40p_rvvi_vif.valid_irq);
        if (cv32e40p_rvvi_vif.valid_irq < valid_irq_prev) begin
          pending_irq_ack = 1;
        end
        valid_irq_prev = cv32e40p_rvvi_vif.valid_irq;
      end
      forever begin : RESET_PENDING_IRQ_ACK
        @(posedge cv32e40p_rvvi_vif.clk);
        if (cv32e40p_rvvi_vif.valid) begin
          if (pc_is_mtvec_addr() && is_mcause_irq()) pending_irq_ack = 0;
        end
      end
      forever begin : SET_PENDING_IRQ_FLAG
        @(negedge cv32e40p_rvvi_vif.clk);
        if (cv32e40p_rvvi_vif.irq_onehot_priority !== prev_irq_onehot_priority) begin
          pending_irq = 0;
          if (enter_hwloop_sub) update_prev_irq_onehot_priority(); // within excp period
          else if ((hwloop_stat_main.execute_instr_in_hwloop[0] | hwloop_stat_main.execute_instr_in_hwloop[1])) begin // within main loop
            if (prev_irq_onehot_priority === 0) update_prev_irq_onehot_priority(); // new pending
            else begin // last irq or any pending irq(s)
              if (!is_irq) pending_irq = 1;
              else begin 
                repeat(2) @(negedge cv32e40p_rvvi_vif.clk);
                if (!is_irq) pending_irq = 1;
                else update_prev_irq_onehot_priority();
              end
            end
          end
          else begin update_prev_irq_onehot_priority(); end // outside hwloop period
        end
      end // SET_PENDING_IRQ_FLAG
      forever begin : IRQ_EXIT
        wait (hwloop_stat_main.execute_instr_in_hwloop[0] | hwloop_stat_main.execute_instr_in_hwloop[1]);
        @(posedge cv32e40p_rvvi_vif.clk);
        if (is_irq && cv32e40p_rvvi_vif.valid && cv32e40p_rvvi_vif.insn == TB_INSTR_MRET) begin
          `uvm_info(_header, $sformatf("DEBUG - IRQ Exit"), UVM_DEBUG);
          is_irq = 0;
        end
      end // IRQ_EXIT
      forever begin : SIGNALS_CHG_WHEN_IS_IRQ_ASSERT
        @(posedge is_irq);
        if (is_ebreakm) begin // TBD: will ebreakm assert trap?
          for (int j=0; j<HWLOOP_NB; j++) begin
            logic [31:0] discarded_insn;
            if (hwloop_stat_main.execute_instr_in_hwloop[j] && lpend_has_pending_irq_main[j]) begin 
              discarded_insn = insn_list_in_hwloop_main[j].pop_back();
              assert(discarded_insn == INSN_EBREAKM);
              void'(hwloop_evt_loc_main[j][DBG_EBREAKM].pop_back());
              hwloop_stat_main.track_lp_cnt[j]++; lpend_has_pending_irq_main[j] = 0;
            end
          end // for
        end
      end // SIGNALS_CHG_WHEN_IS_IRQ_ASSERT

      forever begin : DBG_ENTRY
        // wait (hwloop_stat_main.execute_instr_in_hwloop[0] | hwloop_stat_main.execute_instr_in_hwloop[1]);
        wait (!is_dbg_mode);
        wait (cv32e40p_rvvi_vif.clk && cv32e40p_rvvi_vif.valid && cv32e40p_rvvi_vif.pc_rdata == cv32e40p_rvvi_vif.dm_halt_addr && dcsr_cause_t'(cv32e40p_rvvi_vif.csr_dcsr_cause) inside {EBREAKM, TRIGGER, HALTREQ, STEP}) begin
          dcsr_cause = dcsr_cause_t'(cv32e40p_rvvi_vif.csr_dcsr_cause);
          is_dbg_mode = 1;
          unique case(dcsr_cause)
            EBREAKM : begin /* do nothing */ end
            TRIGGER : begin
                        if (hwloop_stat_main.execute_instr_in_hwloop[1] && !(in_nested_loop0|in_nested_loop0_d1)) begin `IF_CURRENT_IS_MAIN_HWLOOP(1, DBG_TRIG) end
                        else                                                                                      begin `IF_CURRENT_IS_MAIN_HWLOOP(0, DBG_TRIG) end
                      end
            HALTREQ : begin
                        if (hwloop_stat_main.execute_instr_in_hwloop[1] && !(in_nested_loop0|in_nested_loop0_d1)) begin `IF_CURRENT_IS_MAIN_HWLOOP(1, DBG_HALTREQ) end
                        else                                                                                      begin `IF_CURRENT_IS_MAIN_HWLOOP(0, DBG_HALTREQ) end
                      end
            STEP    : begin
                        if (hwloop_stat_main.execute_instr_in_hwloop[1] && !(in_nested_loop0|in_nested_loop0_d1)) begin `IF_CURRENT_IS_MAIN_HWLOOP(1, DBG_STEP) end
                        else                                                                                      begin `IF_CURRENT_IS_MAIN_HWLOOP(0, DBG_STEP) end
                      end
          endcase
          `uvm_info(_header, $sformatf("DEBUG - Debug Mode Entry due to %s", dcsr_cause.name()), UVM_DEBUG);
        end
      end // DBG_ENTRY
      forever begin : DBG_EXIT
        // wait (hwloop_stat_main.execute_instr_in_hwloop[0] | hwloop_stat_main.execute_instr_in_hwloop[1]);
        wait (is_dbg_mode);
        wait (cv32e40p_rvvi_vif.clk && cv32e40p_rvvi_vif.valid && cv32e40p_rvvi_vif.insn == TB_INSTR_DRET) begin
          @(posedge cv32e40p_rvvi_vif.clk) ; @(negedge cv32e40p_rvvi_vif.clk);
          `uvm_info(_header, $sformatf("DEBUG - Debug Mode Exit"), UVM_DEBUG);
          is_dbg_mode = 0; is_ebreakm = 0;
        end
      end // DBG_EXIT
      forever begin : SIGNALS_CHG_WHEN_IS_DBG_MODE_ASSERT
        @(posedge is_dbg_mode);
        lpend_has_pending_irq_main[0] = 0; 
        lpend_has_pending_irq_main[1] = 0;
      end // SIGNALS_CHG_WHEN_IS_DBG_MODE_ASSERT

    join_none // Background threads - END

    forever begin
      @(posedge cv32e40p_rvvi_vif.clk);
      if (cv32e40p_rvvi_vif.valid) begin : VALID_IS_HIGH

        if (enter_hwloop_sub) begin 
          enter_hwloop_sub_cnt++;
          if (is_trap && is_dbg_mode && !cv32e40p_rvvi_vif.csr_dcsr_step && enter_hwloop_sub_cnt == 1) begin : TRAP_DUETO_DBG_ENTRY // exception trap and debug are b2b cycles (except debug step)
            has_pending_trap_due2_dbg = 1; 
          end // TRAP_DUETO_DBG_ENTRY
          else if (pc_is_mtvec_addr() && !is_mcause_irq()) begin : EXCEPTION_ENTRY
            for (int i=0; i<HWLOOP_NB; i++) begin
              if (hwloop_stat_main.execute_instr_in_hwloop[i] && !done_insn_list_capture_d1_main[i]) begin
              case (i)
                0: check_exception_entry(i);
                1: begin
                    if (in_nested_loop0) continue;
                    else check_exception_entry(i);
                   end
              endcase
              end
            end
          end // EXCEPTION_ENTRY
          else if (pc_is_mtvec_addr() && is_mcause_irq()) begin : IRQ_ENTRY
            if (hwloop_stat_main.execute_instr_in_hwloop[0] | hwloop_stat_main.execute_instr_in_hwloop[1]) begin
              if (is_trap && enter_hwloop_sub_cnt == 1) begin : TRAP_DUETO_IRQ_ENTRY // exception trap and irq are b2b cycles
                if (hwloop_stat_main.execute_instr_in_hwloop[0] && lpend_has_pending_irq_main[0]) begin hwloop_stat_main.track_lp_cnt[0]++; lpend_has_pending_irq_main[0] = 0; end // revert lp_cnt
                if (hwloop_stat_main.execute_instr_in_hwloop[1] && lpend_has_pending_irq_main[1]) begin hwloop_stat_main.track_lp_cnt[1]++; lpend_has_pending_irq_main[1] = 0; end // revert lp_cnt
                has_pending_trap_due2_irq = 1; 
                is_ebreak = 0; is_ecall = 0; is_illegal = 0; is_trap = 0;
                enter_hwloop_sub = 0; enter_hwloop_sub_cnt = 0;
                pending_irq = 0;
                `uvm_info(_header, $sformatf("DEBUG - EXCEPTION Entry is replaced with IRQ Entry (higher priority)"), UVM_DEBUG);
                `IF_CURRENT_IS_MAIN_HWLOOP(0, IS_IRQ)
                `IF_CURRENT_IS_MAIN_HWLOOP(1, IS_IRQ)
                update_prev_irq_onehot_priority();
                `uvm_info(_header, $sformatf("DEBUG - IRQ Entry"), UVM_DEBUG);
              end // TRAP_DUETO_IRQ_ENTRY
              is_irq = 1; wait (!is_irq); continue; 
            end
          end // IRQ_ENTRY

          // [optional] todo: for hwloops that outside main code (e.g irq only, dbg only, or irq->dbg); currently commented out due to pending for implementation
          // `CHECK_N_SAMPLE_CSR_HWLOOP(sub);
          // `CHECK_N_SAMPLE_HWLOOP(sub);
          // [optional] todo: mie has effect on irq during exception. Current hwloop tests do not exercise nested irq with mie enabled

          check_exception_exit();
          if (!(is_ebreak || is_ecall || is_illegal || has_pending_trap_due2_dbg || has_pending_trap_due2_irq)) begin
            enter_hwloop_sub = 0; enter_hwloop_sub_cnt = 0; 
          end
          else if (has_pending_trap_due2_dbg) begin
            enter_hwloop_sub = 0; enter_hwloop_sub_cnt = 0;
            is_ebreak = 0; is_ecall = 0; is_illegal = 0; is_trap = 0;
          end
          prev_pc_rdata_sub = cv32e40p_rvvi_vif.pc_rdata;
        end

        else begin : MAIN
          if (pc_is_mtvec_addr() && is_mcause_irq()) begin : IRQ_ENTRY
            if (hwloop_stat_main.execute_instr_in_hwloop[0] | hwloop_stat_main.execute_instr_in_hwloop[1]) begin
              pending_irq = 0;
              `IF_CURRENT_IS_MAIN_HWLOOP(0, IS_IRQ)
              `IF_CURRENT_IS_MAIN_HWLOOP(1, IS_IRQ)
              update_prev_irq_onehot_priority();
              `uvm_info(_header, $sformatf("DEBUG - IRQ Entry"), UVM_DEBUG);
              if (lpend_has_pending_irq_main[0]) begin hwloop_stat_main.track_lp_cnt[0]++; lpend_has_pending_irq_main[0] = 0; end // revert lp_cnt
              if (lpend_has_pending_irq_main[1]) begin hwloop_stat_main.track_lp_cnt[1]++; lpend_has_pending_irq_main[1] = 0; end // revert lp_cnt
              is_irq = 1; wait (!is_irq); continue; 
            end
          end // IRQ_ENTRY
          if (has_pending_trap_due2_irq)  begin
            assert(prev_pc_rdata_main == cv32e40p_rvvi_vif.pc_rdata);
            if (pc_is_mtvec_addr() || (cv32e40p_rvvi_vif.trap && is_trap)) begin is_trap = 1; enter_hwloop_sub = 1; has_pending_trap_due2_irq = 0; continue; end // if pc is exception related
            else begin              is_ebreak = 0; is_ecall = 0; is_illegal = 0; is_trap = 0; enter_hwloop_sub = 0; has_pending_trap_due2_irq = 0; continue; end // if pc is non-exception related
          end
          if (is_dbg_mode)                begin wait (!is_dbg_mode); continue; end
          if (has_pending_trap_due2_dbg)  begin // e.g exception event intercept with debug step
            assert (!dcsr_cause_t'(cv32e40p_rvvi_vif.csr_dcsr_cause) != STEP); // this is not mean for step debug
            if (pc_is_mtvec_addr() || (cv32e40p_rvvi_vif.trap && is_trap)) begin is_trap = 1; enter_hwloop_sub = 1; has_pending_trap_due2_dbg = 0; continue; end // if pc is exception related
            else begin              is_ebreak = 0; is_ecall = 0; is_illegal = 0; is_trap = 0; enter_hwloop_sub = 0; has_pending_trap_due2_dbg = 0; continue; end // if pc is non-exception related
          end
          if (has_trap_due2_dbg_match_trig) begin // e.g exception event intercept with debug trigger
            has_trap_due2_dbg_match_trig = 0;
          end
          if (cv32e40p_rvvi_vif.csr_dcsr_ebreakm && cv32e40p_rvvi_vif.insn == TB_INSTR_EBREAK) is_ebreakm = 1; else is_ebreakm = 0;
          `CHECK_N_SAMPLE_CSR_HWLOOP(main);
          `CHECK_N_SAMPLE_HWLOOP(main);
          if (is_ebreak || is_ecall || is_illegal) enter_hwloop_sub = 1;
          prev_pc_rdata_main = cv32e40p_rvvi_vif.pc_rdata;
        end

      end // VALID_DETECTED
    end // forever

  endtask : run_phase

  function void final_phase(uvm_phase phase);
    super.final_phase(phase);
    if (hwloop_stat_main == hwloop_stat_init) begin
      `uvm_info(_header, $sformatf("DEBUG - No prematured hwloops when test done"), UVM_DEBUG);
    end
    else begin
      `uvm_error(_header, $sformatf("Detected prematured hwloops when test done. Please debug ... "));
    end
  endfunction : final_phase

  function bit is_pc_equal_lpstart(s_csr_hwloop csr_hwloop, int csr_idx=0, int fwd_offset=0, logic [31:0] pc_rdata);
    if (pc_rdata == csr_hwloop.lp_start[csr_idx]+(fwd_offset*4)) return 1;
    else return 0; 
  endfunction: is_pc_equal_lpstart

  function bit is_pc_equal_lpend(s_csr_hwloop csr_hwloop, int csr_idx=0, int rvs_offset=0, logic [31:0] pc_rdata);
    if (pc_rdata == csr_hwloop.lp_end[csr_idx]-4-(rvs_offset*4)) return 1;
    else return 0; 
  endfunction: is_pc_equal_lpend

  function bit is_pc_within_lp(s_csr_hwloop csr_hwloop, int csr_idx=0, logic [31:0] pc_rdata);
    if (pc_rdata >= csr_hwloop.lp_start[csr_idx] && cv32e40p_rvvi_vif.pc_rdata <= csr_hwloop.lp_end[csr_idx]-4) return 1;
    else return 0;
  endfunction : is_pc_within_lp

endclass : uvme_rv32x_hwloop_covg

`endif
