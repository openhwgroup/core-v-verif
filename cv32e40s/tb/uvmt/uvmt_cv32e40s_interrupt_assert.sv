//
// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
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


`default_nettype none


module uvmt_cv32e40s_interrupt_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  (

    input wire clk,   // Gated clock
    input wire clk_i, // Free-running core clock
    input wire rst_ni,

    // Core input wires
    input wire        fetch_enable_i, // external core fetch enable

    // External interrupt interface
    input wire [31:0] irq_i,
    input wire        irq_ack_o,
    input wire [9:0]  irq_id_o,

    // External debug req (for WFI modeling)
    input wire        debug_req_i,
    input wire        debug_mode_q,

    // CSR Interface
    input wire [5:0]  mcause_n, // mcause_n[5]: interrupt, mcause_n[4]: vector
    input wire [31:0] mip,     // machine interrupt pending
    input wire [31:0] mie_q,   // machine interrupt enable
    input wire        mstatus_mie,  // machine mode interrupt enable
    input wire        mstatus_tw,   // "timeout wait"
    input wire [1:0]  mtvec_mode_q, // machine mode interrupt vector mode
    input wire        dcsr_step,

    // IF stage
    input wire        if_stage_instr_req_o,
    input wire        if_stage_instr_rvalid_i, // Instruction word is valid
    input wire [31:0] if_stage_instr_rdata_i, // Instruction word data
    input wire [ 1:0] alignbuf_outstanding, // Alignment buffer's number of outstanding transactions

    // EX stage
    input wire        ex_stage_instr_valid, // EX pipeline stage has valid input

    // WB stage (determines executed instructions)
    input wire              wb_stage_instr_err_i,      // OBI "err"
    input wire              wb_stage_instr_valid_i,    // instruction word is valid
    input wire [31:0]       wb_stage_instr_rdata_i,    // Instruction word data
    input wire mpu_status_e wb_stage_instr_mpu_status, // MPU read/write errors
    input wire              wb_kill,
    input wire              wb_trigger,
    input wire              wb_valid,

    // Load-store unit status
    input wire              lsu_busy,

    // Privilege
    input wire privlvl_t    priv_lvl,

    // Determine whether to cancel instruction if branch taken
    input wire  branch_taken_ex,

    // WFI/WFE Interface
    input wire  core_sleep_o,
    input wire  wu_wfe_i,

    // OBI
    input wire          mpu_instr_rvalid,
    uvma_obi_memory_if_t  obi_instr_if,
    uvma_obi_memory_if_t  obi_data_if,

    // Writebuffer
    input wire write_buffer_state_e  writebufstate,

    // RVFI
    uvma_rvfi_instr_if_t  rvfi,

    // NMI
    input wire  pending_nmi,

    // Support Interface
    uvmt_cv32e40s_support_logic_module_o_if_t.slave_mp  support_if
  );

  // ---------------------------------------------------------------------------
  // Local parameters
  // ---------------------------------------------------------------------------
  localparam NUM_IRQ        = 32;
  localparam VALID_IRQ_MASK = 32'hffff_0888; // Valid external interrupt signals

  localparam WFI_INSTR_DATA = 32'h10500073;
  localparam WFE_INSTR_DATA = 32'h8C000073;

  localparam WFI_TO_CORE_SLEEP_LATENCY = 2;
  localparam WFI_WAKEUP_LATENCY = 40;

  // ---------------------------------------------------------------------------
  // Local variables
  // ---------------------------------------------------------------------------
  string info_tag = "CV32E40S_IRQ_ASSERT";

  wire [31:0] pending_enabled_irq;
  wire [31:0] pending_enabled_irq_q;

  reg[31:0] irq_q;

  reg[31:0] next_irq;
  reg       next_irq_valid;

  reg[31:0] next_irq_q;
  reg       next_irq_valid_q;
  reg[31:0] saved_mie_q;

  reg[31:0] expected_irq;
  logic     expected_irq_ack;
  wire      is_mmode_mstatusmie = (priv_lvl == PRIV_LVL_M) && mstatus_mie;
  wire      is_umode_miemip     = (priv_lvl == PRIV_LVL_U) && (mie_q & mip);

  reg[31:0] last_instr_rdata;

  // ---------------------------------------------------------------------------
  // Clocking blocks
  // ---------------------------------------------------------------------------

  // Single clock, single reset design, use default clocking
  default clocking @(posedge clk_i); endclocking
  default disable iff !(rst_ni);

  // ---------------------------------------------------------------------------
  // Begin module code
  // ---------------------------------------------------------------------------
  assign pending_enabled_irq   = irq_i & mie_q;
  assign pending_enabled_irq_q = irq_q & mie_q;

  // ---------------------------------------------------------------------------
  // Interrupt interface checks
  // ---------------------------------------------------------------------------

  // irq_ack_o is always a pulse
  property p_irq_ack_o_pulse;
    irq_ack_o |=> !irq_ack_o;
  endproperty
  a_irq_ack_o_pulse: assert property(p_irq_ack_o_pulse)
    else
      `uvm_error(info_tag,
                 "Interrupt ack was asserted for more than one cycle");

  // irq_id_o is never a reserved irq
  let valid_irq_mask_index = irq_id_o[ $clog2($bits(VALID_IRQ_MASK)) - 1 : 0 ];
  property p_irq_id_o_not_reserved;
    irq_ack_o |-> VALID_IRQ_MASK[ valid_irq_mask_index ];
  endproperty
  a_irq_id_o_not_reserved: assert property(p_irq_id_o_not_reserved)
    else
      `uvm_error(info_tag,
                 $sformatf("int_id_o output is 0x%0x which is reserved", irq_id_o));

  // irq_id_o is never a disabled irq
  let mie_q_index = irq_id_o[ $clog2($bits(mie_q)) - 1 : 0 ];
  property p_irq_id_o_mie_enabled;
    irq_ack_o |-> mie_q[ mie_q_index ];
  endproperty
  a_irq_id_o_mie_enabled: assert property(p_irq_id_o_mie_enabled)
    else
      `uvm_error(info_tag,
                 $sformatf("irq_id_o output is 0x%0x which is disabled in MIE: 0x%08x", irq_id_o, mie_q));

  // irq_ack_o cannot be asserted without mstatus_mie or U-mode
  a_irq_id_o_mstatus_mie_enabled: assert property (
    irq_ack_o
    |->
    is_mmode_mstatusmie ^ is_umode_miemip
  ) else `uvm_error(info_tag, $sformatf("interrupt handler taken but unexpected mie"));
  cov_irq_id_o_mstatus_mstatusmie: cover property (irq_ack_o ##0 is_mmode_mstatusmie);
  cov_irq_id_o_mstatus_miemip:     cover property (irq_ack_o ##0 is_umode_miemip);


  // ---------------------------------------------------------------------------
  // Interrupt CSR checks
  // ---------------------------------------------------------------------------

  // Coverage for individual interupt assertions
  sequence s_irq_taken(irq);
    irq_i[irq] ##0 mie_q[irq] ##0 mstatus_mie ##0 irq_ack_o ##0 irq_id_o == irq;
  endsequence : s_irq_taken

  // Interrupt fired, global interrupts enabled, but not taken due to global MSTATUS.MIE setting
  property p_irq_masked(irq);
    irq_i[irq] ##0 !mie_q[irq] ##0 mstatus_mie;
  endproperty : p_irq_masked

  // Interrupt fired and locally enabled in MIE, but masked due to MSTATUS_MIE
  property p_irq_masked_mstatus(irq);
    irq_i[irq] ##0 mie_q[irq] ##0 !mstatus_mie;
  endproperty : p_irq_masked_mstatus

  // Interrupt taken
  property p_irq_taken(irq);
    s_irq_taken(irq);
  endproperty : p_irq_taken

  // Interrupt enabled via MIE locally masked
  property p_irq_masked_then_enabled(irq);
    irq_i[irq] ##0 !mie_q[irq] ##0 mstatus_mie ##1 irq_i[irq] ##0 mie_q[irq] ##0 mstatus_mie;
  endproperty : p_irq_masked_then_enabled

  // Interrupt enabled via MSTATUS_MIE locally masked
  property p_irq_masked_mstatus_then_enabled(irq);
    irq_i[irq] ##0 mie_q[irq] ##0 !mstatus_mie ##1 irq_i[irq] ##0 mie_q[irq] ##0 mstatus_mie;
  endproperty : p_irq_masked_mstatus_then_enabled

  // Interrupt request deasserted when enabled but not acked
  property p_irq_deasserted_while_enabled_not_acked(irq);
    irq_i[irq] ##0 mie_q[irq] ##0 mstatus_mie ##0 !irq_ack_o ##1
    !irq_i[irq] ##0 !irq_ack_o;
  endproperty : p_irq_deasserted_while_enabled_not_acked

  // Interrupt taken in each supported mtvec mode
  property p_irq_in_mtvec(irq, mtvec);
    s_irq_taken(irq) ##0 mtvec_mode_q == mtvec;
  endproperty
  generate for(genvar gv_i = 0; gv_i < NUM_IRQ; gv_i++) begin : gen_irq_cov
    if (VALID_IRQ_MASK[gv_i]) begin : gen_valid
      cov_irq_masked: cover property(p_irq_masked(gv_i));
      cov_irq_masked_mstatus: cover property(p_irq_masked_mstatus(gv_i));
      cov_irq_taken: cover property(p_irq_taken(gv_i));
      cov_irq_masked_then_enabled: cover property(p_irq_masked_then_enabled(gv_i));
      cov_irq_masked_mstatus_then_enabled: cover property(p_irq_masked_mstatus_then_enabled(gv_i));
      cov_irq_deasserted_while_enabled_not_acked: cover property(p_irq_deasserted_while_enabled_not_acked(gv_i));
      cov_irq_in_mtvec_fixed: cover property(p_irq_in_mtvec(gv_i, 0));
      cov_irq_in_mtvec_vector: cover property(p_irq_in_mtvec(gv_i, 1));
    end
  end
  endgenerate

  // Detect arbitration of interrupt assertion
  always @* begin
    next_irq_valid = 1'b0;
    next_irq = '0;
    casex ({pending_enabled_irq_q[31:16], pending_enabled_irq_q[11], pending_enabled_irq_q[3], pending_enabled_irq_q[7]})
      19'b1???_????_????_????_???: begin next_irq = 'd31; next_irq_valid = '1; end
      19'b01??_????_????_????_???: begin next_irq = 'd30; next_irq_valid = '1; end
      19'b001?_????_????_????_???: begin next_irq = 'd29; next_irq_valid = '1; end
      19'b0001_????_????_????_???: begin next_irq = 'd28; next_irq_valid = '1; end
      19'b0000_1???_????_????_???: begin next_irq = 'd27; next_irq_valid = '1; end
      19'b0000_01??_????_????_???: begin next_irq = 'd26; next_irq_valid = '1; end
      19'b0000_001?_????_????_???: begin next_irq = 'd25; next_irq_valid = '1; end
      19'b0000_0001_????_????_???: begin next_irq = 'd24; next_irq_valid = '1; end
      19'b0000_0000_1???_????_???: begin next_irq = 'd23; next_irq_valid = '1; end
      19'b0000_0000_01??_????_???: begin next_irq = 'd22; next_irq_valid = '1; end
      19'b0000_0000_001?_????_???: begin next_irq = 'd21; next_irq_valid = '1; end
      19'b0000_0000_0001_????_???: begin next_irq = 'd20; next_irq_valid = '1; end
      19'b0000_0000_0000_1???_???: begin next_irq = 'd19; next_irq_valid = '1; end
      19'b0000_0000_0000_01??_???: begin next_irq = 'd18; next_irq_valid = '1; end
      19'b0000_0000_0000_001?_???: begin next_irq = 'd17; next_irq_valid = '1; end
      19'b0000_0000_0000_0001_???: begin next_irq = 'd16; next_irq_valid = '1; end
      19'b0000_0000_0000_0000_1??: begin next_irq = 'd11; next_irq_valid = '1; end
      19'b0000_0000_0000_0000_01?: begin next_irq = 'd3; next_irq_valid = '1; end
      19'b0000_0000_0000_0000_001: begin next_irq = 'd7; next_irq_valid = '1; end
    endcase
  end

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      irq_q <= 0;
      next_irq_q <= 0;
      next_irq_valid_q <= 0;
      saved_mie_q <= 0;
    end
    else begin
      irq_q <= irq_i;
      next_irq_q <= next_irq;
      next_irq_valid_q <= next_irq_valid;
      saved_mie_q <= mie_q;
    end
  end

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)
      expected_irq <= 0;
    else
      expected_irq <= next_irq_q;
  end

  assign expected_irq_ack = next_irq_valid && (is_mmode_mstatusmie || is_umode_miemip);

  // Check expected interrupt wins
  property p_irq_arb;
    irq_ack_o |-> irq_id_o == next_irq;
  endproperty
  a_irq_arb: assert property(p_irq_arb)
    else
      `uvm_error(info_tag,
                 $sformatf("Expected winning interrupt: %0d, actual interrupt: %0d", next_irq, irq_id_o))

  // Check that an interrupt is expected
  property p_irq_expected;
    irq_ack_o |-> expected_irq_ack;
  endproperty
  a_irq_expected: assert property(p_irq_expected)
    else `uvm_error(info_tag, $sformatf("Did not expect interrupt ack: %0d", irq_id_o))

  // ---------------------------------------------------------------------------
  // The infamous "first" flag (kludge for $past() handling of t=0 values)
  // Would like to use a leading ##1 in the property instead but this currently
  // does not work with dsim
  // ---------------------------------------------------------------------------
  reg first;
  always @(posedge clk or negedge rst_ni)
    if (!rst_ni)
      first <= 1'b1;
    else
      first <= 1'b0;

  // mip reflects flopped interrupt inputs (irq_i) regardless of other configuration
  // Note that this runs on the gated clock
  property p_mip_irq_i;
    @(posedge clk)
      !first |-> mip == ($past(irq_i) & VALID_IRQ_MASK);
  endproperty
  a_mip_irq_i: assert property(p_mip_irq_i)
    else
      `uvm_error(info_tag,
                 $sformatf("MIP of 0x%08x does not follow flopped irq_i input: 0x%08x", mip, $past(irq_i)));

  // mip should not be reserved
  property p_mip_not_reserved;
    (mip & ~VALID_IRQ_MASK) == 0;
  endproperty
  a_mip_not_reserved: assert property(p_mip_not_reserved)
    else
      `uvm_error(info_tag,
                 $sformatf("MIP of reserved interrupt is asserted: mip = 0x%08x", mip));

  // ---------------------------------------------------------------------------
  // Instruction coverage when taking an interrupt
  // ---------------------------------------------------------------------------
  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      last_instr_rdata <= '0;
    end
    else if (wb_stage_instr_valid_i) begin
      last_instr_rdata <= wb_stage_instr_rdata_i;
    end
  end


  // ---------------------------------------------------------------------------
  // WFI Checks
  // ---------------------------------------------------------------------------
  wire logic is_wfi;
  assign is_wfi = wb_stage_instr_valid_i                     &&
                  (wb_stage_instr_rdata_i == WFI_INSTR_DATA) &&
                  !wb_stage_instr_err_i                      &&
                  !((priv_lvl == PRIV_LVL_U) && mstatus_tw)  &&
                  (wb_stage_instr_mpu_status == MPU_OK)      &&
                  !wb_kill                                   &&
                  !debug_mode_q;
  wire logic is_wfe;
  assign is_wfe = wb_stage_instr_valid_i                     &&
                  (wb_stage_instr_rdata_i == WFE_INSTR_DATA) &&
                  !((priv_lvl == PRIV_LVL_U) && mstatus_tw)  &&
                  !wb_stage_instr_err_i                      &&
                  (wb_stage_instr_mpu_status == MPU_OK)      &&
                  !wb_kill                                   &&
                  !debug_mode_q;

  wire logic pipeline_ready_for_wfi;
  assign pipeline_ready_for_wfi = (alignbuf_outstanding == 0) && !lsu_busy;

  logic  wb_wfi_wfe_invalidated;
  assign wb_wfi_wfe_invalidated = (
    !wb_stage_instr_valid_i                  ||
    (wb_stage_instr_mpu_status != MPU_OK)    ||
    wb_stage_instr_err_i                     ||
    wb_kill                                  ||
    debug_mode_q                             ||
    ((priv_lvl == PRIV_LVL_U) && mstatus_tw) ||
    dcsr_step
  );

  logic  is_wfi_wfe_in_wb;
  assign is_wfi_wfe_in_wb = (
    (wb_stage_instr_rdata_i  inside  {WFI_INSTR_DATA, WFE_INSTR_DATA})  &&
    !wb_wfi_wfe_invalidated
  );

  logic is_wfi_wfe_in_wb_q1;
  logic is_wfi_wfe_in_wb_q2;
  always @(posedge clk_i) begin
    is_wfi_wfe_in_wb_q1 <= is_wfi_wfe_in_wb;
    is_wfi_wfe_in_wb_q2 <= is_wfi_wfe_in_wb_q1;
  end

  logic [31:0]  bus_data_outstanding;
  logic [31:0]  bus_instr_outstanding;
  assign bus_instr_outstanding = support_if.alignment_buff_addr_ph_cnt;
  assign bus_data_outstanding  = support_if.data_bus_v_addr_ph_cnt;

  logic  is_wfi_wfe_blocked;
  assign is_wfi_wfe_blocked = (
    |bus_instr_outstanding        ||
    |$past(bus_instr_outstanding) ||  // Arbitrary uarch decision
    |bus_data_outstanding         ||
    |$past(bus_data_outstanding)  ||  // Arbitrary uarch decision
    obi_instr_if.req              ||
    obi_data_if.req               ||
    (writebufstate != WBUF_EMPTY)
    // TODO:silabs-krdosvik (xif): add bustransaction for x-interface
  );

  logic  should_wfi_wfe_awaken;
  assign should_wfi_wfe_awaken = (
    (|pending_enabled_irq)  ||
    debug_req_i             ||
    pending_nmi             ||
    wb_trigger              ||
    (wu_wfe_i && is_wfe)
  );

  logic  model_sleepmode;
  always_latch begin
    if (!rst_ni) begin
      model_sleepmode <= 1'b 0;
    end

    if (
      is_wfi_wfe_in_wb  &&
      is_wfi_wfe_in_wb_q2)  // Arbitrary uarch decision (2 cycles)
    begin
      model_sleepmode <= 1'b 1;
    end

    if (is_wfi_wfe_blocked) begin
      model_sleepmode <= 1'b 0;
    end

    if (should_wfi_wfe_awaken) begin
      model_sleepmode <= 1'b 0;
    end
  end

  // Check expectations for sleep mode

  a_wfi_assert_sleepmode_expected: assert property (
    model_sleepmode === core_sleep_o
  ) else `uvm_error(info_tag, "core_sleep_o must matchexpectations");

  a_wfi_assert_sleepmode_nodbg: assert property (
    debug_mode_q
    |->
    !model_sleepmode
  ) else `uvm_error(info_tag, "there is no sleeping in debug");

  a_wfi_assert_sleepmode_fellreason: assert property (
    $past(is_wfi_wfe_in_wb)  &&
    !is_wfi_wfe_in_wb
    |->
    $past(wb_valid)
    or
    ((rvfi.rvfi_valid [->1]) ##0 (rvfi.rvfi_dbg == DBG_CAUSE_HALTREQ))
  ) else `uvm_error(info_tag, "wfe mustn't leave wb unexpectedly");

  cov_wfi_assert_sleepmode_fellreason_valid: cover property (
    $fell(is_wfi_wfe_in_wb) && $past(wb_valid)
  );

  cov_wfi_assert_sleepmode_fellreason_killed: cover property (
    $fell(is_wfi_wfe_in_wb) && wb_kill
  );


  // Blocked wfi/wfe stay in wb (unless excused)

  a_wfi_assert_sleepmode_wait: assert property (
    is_wfi_wfe_in_wb    &&
    is_wfi_wfe_blocked  &&
    !should_wfi_wfe_awaken
    |=>
    is_wfi_wfe_in_wb
    or
    $past(support_if.recorded_dbg_req)
    or
    ((rvfi.rvfi_valid [->1]) ##0 (rvfi.rvfi_trap.debug_cause == DBG_CAUSE_TRIGGER))
  ) else `uvm_error(info_tag, "blocked wfi/wfe must remain in wb unless special conditions");


  // Sanity check that sleep mode wasn't prematurely entered

  a_wfi_assert_sleepmode_no_ivalid: assert property (
    core_sleep_o
    |->
    !mpu_instr_rvalid && !obi_instr_if.rvalid
  ) else `uvm_error(info_tag, "shouldn't enter sleep if outstanding iside");

  a_wfi_assert_sleepmode_no_dvalid: assert property (
    core_sleep_o
    |->
    !obi_data_if.rvalid
  ) else `uvm_error(info_tag, "shouldn't enter sleep if outstanding dside");

  a_wfi_assert_sleepmode_no_wbuf: assert property (
    core_sleep_o
    |->
    (writebufstate == WBUF_EMPTY)
  ) else `uvm_error(info_tag, "shouldn't enter sleep if wbuf non-empty");


  // Check wfi/wfe retirement conditions

  a_wfi_assert_sleepmode_retire0: assert property (
    $rose(is_wfi_wfe_in_wb)
    |->
    (wb_valid == (dcsr_step && !debug_req_i))
  ) else `uvm_error(info_tag, "1st cycle retire only on step");

  a_wfi_assert_sleepmode_retire1: assert property (
    $rose(is_wfi_wfe_in_wb_q1)  &&
    is_wfi_wfe_in_wb
    |->
    (wb_valid == should_wfi_wfe_awaken)
    or
    ((rvfi.rvfi_valid [->1]) ##0 (rvfi.rvfi_trap.debug_cause == DBG_CAUSE_TRIGGER))
  ) else `uvm_error(info_tag, "2nd cycle can retire on 'premature' 'wakeup'");

  a_wfi_assert_sleepmode_retire2: assert property (
    is_wfi_wfe_in_wb_q2  &&
    is_wfi_wfe_in_wb_q1  &&
    is_wfi_wfe_in_wb
    |->
    (wb_valid == should_wfi_wfe_awaken)
  ) else `uvm_error(info_tag, ">2nd cycle retire only on wake");


  // Confirm the uarch sleep delay is as expected (2 cycles)

  a_wfi_assert_sleepmode_nodly0: assert property (
    $rose(is_wfi_wfe_in_wb)
    |->
    !core_sleep_o
  ) else `uvm_error(info_tag, "1st cycle in wb is too early to sleep");

  a_wfi_assert_sleepmode_nodly1: assert property (
    $rose( $past(is_wfi_wfe_in_wb, 1) )
    |->
    !core_sleep_o
  ) else `uvm_error(info_tag, "2nd cycle in wb is too early to sleep");

  for (genvar i = 2; i < 8; i++) begin: gen_wfi_assert_sleepmode_nodlyn_outer
    for (genvar onoff = 0; onoff < 2; onoff++) begin: gen_wfi_assert_sleepmode_nodlyn_inner
      cov_wfi_assert_sleepmode_nodlyn: cover property (
        $rose( $past(is_wfi_wfe_in_wb, i) )
        ##0
        (core_sleep_o == onoff)
      );
    end
  end

  // Check conditions denying sleep

  a_wfi_assert_core_not_ready: assert property (
    !pipeline_ready_for_wfi |-> !core_sleep_o
  ) else `uvm_error(info_tag, "no sleep before pipeline ready");

  a_wfi_assert_no_entry: assert property (
    (|alignbuf_outstanding || |lsu_busy)
    |=>
    !core_sleep_o
  ) else `uvm_error(info_tag, "no sleep before no outstanding");

  a_wfi_assert_irq_exit: assert property (
    pending_enabled_irq
    |->
    !core_sleep_o
  ) else `uvm_error(info_tag, "no sleep when pending irqs");

  a_wfi_assert_debug_exit: assert property (
    debug_req_i
    |->
    !core_sleep_o
  ) else `uvm_error(info_tag, "no sleep when pending debug");


  // core_sleep_o leads to rvfi_valid

  property  p_wfi_assert_to_rvfi;
    core_sleep_o
    ##1
    (rvfi.rvfi_valid [->1])
    |->
    (rvfi.rvfi_insn  inside  {WFI_INSTR_DATA, WFE_INSTR_DATA})
    ;
    // TODO:INFO:silabs-robin  Checking the inverse case gets complicated by uarch
  endproperty : p_wfi_assert_to_rvfi

  a_wfi_assert_to_rvfi: assert property (p_wfi_assert_to_rvfi)
    else `uvm_error(info_tag, "sleeping wfi/wfe must retire to rvfi");


  // core_sleep_o must come, or WFI/WFE must finish

  property  p_wfi_assert_coresleepo;
    ((is_wfi_wfe_in_wb && !should_wfi_wfe_awaken) [*WFI_TO_CORE_SLEEP_LATENCY])
    |=>
         (core_sleep_o && !wb_valid)
      || (is_wfi_wfe_in_wb && !should_wfi_wfe_awaken && !wb_valid)
      || (should_wfi_wfe_awaken && wb_valid)
    ;
  endproperty : p_wfi_assert_coresleepo

  property  p_wfi_assert_coresleepo_ideal_cond;
        ((is_wfi_wfe_in_wb && !should_wfi_wfe_awaken) [*WFI_TO_CORE_SLEEP_LATENCY])
     ##0 !should_wfi_wfe_awaken && pipeline_ready_for_wfi
     ##1 !should_wfi_wfe_awaken
    |->
    (core_sleep_o && !wb_valid)
    ;
  endproperty : p_wfi_assert_coresleepo_ideal_cond

  a_wfi_assert_coresleepo: assert property (
    p_wfi_assert_coresleepo
  ) else `uvm_error(info_tag, "no retire until sleep or giveup");

  a_wfi_assert_coresleepo_ideal_cond: assert property (
    p_wfi_assert_coresleepo_ideal_cond
  ) else `uvm_error(info_tag, "no retire until sleep or giveup");

  // WFI assertion will assert core_sleep_o (in WFI_TO_CORE_SLEEP_LATENCY cycles after wb, given ideal conditions)
  cov_wfi_assert_core_sleep_long: cover property(
    (
      p_wfi_assert_coresleepo_ideal_cond
    ) and
    (
      ((is_wfi_wfe_in_wb == 1) && (is_wfi_wfe_blocked == 1) && (core_sleep_o == 0)) [*1:$]  ##1
      ((is_wfi_wfe_in_wb == 1) && (is_wfi_wfe_blocked == 0) && (core_sleep_o == 0)) [*1:$]  ##1
      ((is_wfi_wfe_in_wb == 1) && (is_wfi_wfe_blocked == 0) && (core_sleep_o == 1)) [*1:$]
    )
  );


  // core_sleep_o deassertion should result in the wfi/wfe instruction retiring
  property p_core_sleep_deassert;
    core_sleep_o ##1 $fell(core_sleep_o) |-> wb_valid;
  endproperty
  a_core_sleep_deassert: assert property(p_core_sleep_deassert)
    else
      `uvm_error(info_tag,
                 "Deassertion of core_sleep_o in WFI not followed by WFI wakeup");

  // When WFI deasserts the core should be awake
  property p_wfi_deassert_core_sleep_o;
    core_sleep_o ##1 |pending_enabled_irq |-> !core_sleep_o;
  endproperty
  a_wfi_deassert_core_sleep_o: assert property(p_wfi_deassert_core_sleep_o)
    else
      `uvm_error(info_tag,
                 "Deassertion of WFI occurred and core is still asleep");

  // Outside of WFI, the core should not sleep
  a_wfi_deny_core_sleep_o: assert property (
    !is_wfi_wfe_in_wb |-> !core_sleep_o
  ) else
    `uvm_error(info_tag, "Only WFI should trigger core sleep");

  // WFI wakeup to next instruction fetch/execution
  property p_wfi_wake_to_instr_fetch;
    disable iff (!rst_ni || !fetch_enable_i || debug_mode_q)
    $fell(core_sleep_o)
    |=>
    ##[0:WFI_WAKEUP_LATENCY]
      ($rose(if_stage_instr_req_o)  // IF starts fetching again
        || $rose(ex_stage_instr_valid));  // Or continue with prefetched data
  endproperty
  a_wfi_wake_to_instr_fetch: assert property(p_wfi_wake_to_instr_fetch)
    else
      `uvm_error(info_tag,
                 $sformatf("Core did not start fetching %0d cycles after WFI completed", WFI_WAKEUP_LATENCY));

  // Cover property, detect sleep deassertion due to asserted and non-asserted interrupts
  property p_wfi_wake_mstatus_mie(irq, mie);
    irq_i[irq] && mie_q[irq] && mstatus_mie == mie ##1 $fell(is_wfi_wfe_in_wb);
  endproperty

  generate for(genvar gv_i = 0; gv_i < 32; gv_i++) begin : gen_wfi_cov
    if (VALID_IRQ_MASK[gv_i]) begin
      cov_wfi_wake_mstatus_mie_0: cover property(p_wfi_wake_mstatus_mie(gv_i, 0));
      cov_wfi_wake_mstatus_mie_1: cover property(p_wfi_wake_mstatus_mie(gv_i, 1));
    end
  end
  endgenerate


endmodule : uvmt_cv32e40s_interrupt_assert


`default_nettype wire
