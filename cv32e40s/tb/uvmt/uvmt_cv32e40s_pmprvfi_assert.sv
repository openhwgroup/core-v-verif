`default_nettype none

module uvmt_cv32e40s_pmprvfi_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import cv32e40s_rvfi_pkg::*;
#(
  parameter int  PMP_GRANULARITY = 0,
  parameter int  PMP_NUM_REGIONS = 0
)(
  // Clock and Reset
  input wire  clk_i,
  input wire  rst_ni,

  // RVFI
  input wire         rvfi_valid,
  input wire [31:0]  rvfi_insn,
  input wire [ 1:0]  rvfi_mode,
  input rvfi_trap_t  rvfi_trap,
  input wire [PMP_MAX_REGIONS/4-1:0][31:0]  rvfi_csr_pmpcfg_rdata,
  input wire [PMP_MAX_REGIONS-1:0]  [31:0]  rvfi_csr_pmpaddr_rdata,
  input wire [31:0]  rvfi_csr_mseccfg_rdata,
  input wire [31:0]  rvfi_csr_mseccfgh_rdata,
  input wire [ 4:0]  rvfi_rd_addr,
  input wire [31:0]  rvfi_rd_wdata,
  input wire [ 4:0]  rvfi_rs1_addr,
  input wire [31:0]  rvfi_rs1_rdata
);

  // Defines
  localparam logic [1:0] MODE_U = 2'b 00;
  localparam logic [1:0] MODE_M = 2'b 11;

  localparam logic [5:0] EXC_INSTR_ACC_FAULT    = 6'd 1;
  localparam logic [5:0] EXC_ILL_INSTR          = 6'd 2;
  localparam logic [5:0] EXC_INSTR_BUS_FAULT    = 6'd 48;
  localparam logic [5:0] EXC_INSTR_CHKSUM_FAULT = 6'd 49;

  localparam logic [2:0] DBG_TRIGGER = 3'd 2;

  localparam int NUM_CFG_REGS  = 16;
  localparam int NUM_ADDR_REGS = 64;

  localparam int CSRADDR_FIRST_PMPCFG  = 12'h 3A0;
  localparam int CSRADDR_FIRST_PMPADDR = 12'h 3B0;


  // Defaults
  default clocking @(posedge clk_i); endclocking
  default disable iff !(rst_ni);


  // Helper signals
  wire  is_rvfi_csr_instr =
    rvfi_valid  &&
    (rvfi_insn[6:0] == 7'b 1110011)  &&
    (rvfi_insn[14:12] inside {1, 2, 3, 5, 6, 7});
  wire  is_rvfi_exception =
    rvfi_valid  &&
    rvfi_trap.trap  &&
    rvfi_trap.exception;
  wire  is_rvfi_exc_ill_instr =
    is_rvfi_exception  &&
    (rvfi_trap.exception_cause == EXC_ILL_INSTR);
  wire  is_rvfi_exc_instr_acc_fault =
    is_rvfi_exception  &&
    (rvfi_trap.exception_cause == EXC_INSTR_ACC_FAULT);
  wire  is_rvfi_exc_instr_bus_fault=
    is_rvfi_exception  &&
    (rvfi_trap.exception_cause == EXC_INSTR_BUS_FAULT);
  wire  is_rvfi_exc_instr_chksum_fault=
    is_rvfi_exception  &&
    (rvfi_trap.exception_cause == EXC_INSTR_CHKSUM_FAULT);
  wire  is_rvfi_dbg_trigger =
    rvfi_valid  &&
    rvfi_trap.debug  &&
    (rvfi_trap.debug_cause == DBG_TRIGGER);
  wire  is_rvfi_csr_read_instr =
    is_rvfi_csr_instr  &&
    rvfi_rd_addr;
    // TODO:ropeders double check correctness
  wire  is_rvfi_csr_write_instr =
    is_rvfi_csr_instr  &&
    !((rvfi_insn[13:12] inside {2'b 10, 2'b 11}) && !rvfi_rs1_addr);  // CSRRS/C[I] w/ rs1=x0/0
    // TODO:ropeders double check correctness

  pmp_csr_t  pmp_csr_rvfi_rdata;
  for (genvar i = 0; i < PMP_MAX_REGIONS; i++) begin: gen_pmp_csr_readout
    localparam pmpcfg_reg_i    = i / 4;
    localparam pmpcfg_field_hi = (8 * (i % 4)) + 7;
    localparam pmpcfg_field_lo = (8 * (i % 4));

    assign pmp_csr_rvfi_rdata.cfg[i]  = rvfi_csr_pmpcfg_rdata[pmpcfg_reg_i][pmpcfg_field_hi : pmpcfg_field_lo];
    assign pmp_csr_rvfi_rdata.addr[i] = rvfi_csr_pmpaddr_rdata[i];  // TODO:ropeders is this assignment correct?
  end
  assign pmp_csr_rvfi_rdata.mseccfg = {rvfi_csr_mseccfgh_rdata, rvfi_csr_mseccfg_rdata};


  // Assertions

  // PMP CSRs only accessible from M-mode
  property p_csrs_mmode_only;
    is_rvfi_csr_instr  &&
    (rvfi_mode == MODE_U)  &&
    (rvfi_insn[31:20] inside {['h3A0 : 'h3EF], 'h747, 'h757})
    |->
    is_rvfi_exc_ill_instr  ^
    is_rvfi_exc_instr_acc_fault  ^
    is_rvfi_dbg_trigger ^
    is_rvfi_exc_instr_bus_fault  ^
    is_rvfi_exc_instr_chksum_fault;
  endproperty : p_csrs_mmode_only
  a_csrs_mmode_only: assert property (
    p_csrs_mmode_only
  );
  cov_csrs_mmod_only: cover property (
    p_csrs_mmode_only  and  is_rvfi_exc_ill_instr
  );

  // NAPOT, some bits read as ones, depending on G
  if (PMP_GRANULARITY >= 2) begin: gen_napot_ones_g2
    //TODO:ropeders no magic numbers
    for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_napot_ones_i
      a_napot_ones: assert property (
        rvfi_valid  &&
        pmp_csr_rvfi_rdata.cfg[i].mode[1]
        |->
        (pmp_csr_rvfi_rdata.addr[i][PMP_GRANULARITY-2:0] == '1)
      );
    end
  end

  // OFF/TOR, some bits read as zeros, depending on G
  if (PMP_GRANULARITY >= 1) begin: gen_all_zeros_g1
    for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_all_zeros_i
      a_all_zeros: assert property (
        rvfi_valid  &&
        (pmp_csr_rvfi_rdata.cfg[i].mode[1] === 1'b 0)
        |->
        (pmp_csr_rvfi_rdata.addr[i][PMP_GRANULARITY-1:0] == '0)
      );
    end
  end

  // Software-view on PMP CSRs matches RVFI-view
  for (genvar i = 0; i < NUM_CFG_REGS; i++) begin: gen_swview_cfg
    a_pmpcfg_swview: assert property (
      // TODO:ropeders no magic numbers
      is_rvfi_csr_read_instr  &&
      (rvfi_insn[31:20] == (CSRADDR_FIRST_PMPCFG + i))
      |->
      (rvfi_rd_wdata == rvfi_csr_pmpcfg_rdata[i])
    );
  end
  for (genvar i = 0; i < NUM_ADDR_REGS; i++) begin: gen_swview_addr
    a_pmpaddr_swview: assert property (
      // TODO:ropeders no magic numbers
      is_rvfi_csr_read_instr  &&
      (rvfi_insn[31:20] == (CSRADDR_FIRST_PMPADDR + i))
      |->
      (rvfi_rd_wdata == rvfi_csr_pmpaddr_rdata[i])
    );
  end

  // Software views does not change underlying register value
  property p_storage_unaffected(i);
    logic [31:0] pmpaddr;
    accept_on (
      is_rvfi_csr_write_instr  &&
      (rvfi_insn[31:20] == (CSRADDR_FIRST_PMPADDR + i))
    )
      rvfi_valid  ##0
      pmp_csr_rvfi_rdata.cfg[i].mode[1]  ##0
      (1, pmpaddr = pmp_csr_rvfi_rdata.addr[i])
      ##1
      (rvfi_valid [->1])  ##0
      (pmp_csr_rvfi_rdata.cfg[i].mode[1] == 1'b 0)
      ##1
      (rvfi_valid [->1])  ##0
      pmp_csr_rvfi_rdata.cfg[i].mode[1]
    |->
    (pmp_csr_rvfi_rdata.addr[i][31:0] == pmpaddr);
    // Note, this _can_ be generalized more, but at a complexity/readability cost
  endproperty : p_storage_unaffected
  for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_storage_unaffected
    a_storage_unaffected: assert property (
      p_storage_unaffected(i)
    );
  end

  // TODO:ropeders "uvm_error" on all assertions

  // Software-view can read the granularity level
  a_granularity_determination: assert property (
    (is_rvfi_csr_instr && (rvfi_insn[14:12] == 3'b 001)) &&  // CSRRW instr,
    (rvfi_insn[31:20] == (CSRADDR_FIRST_PMPADDR + 0))    &&  // to a "pmpaddr" CSR,
    ((rvfi_rs1_rdata == '1) && rvfi_rs1_addr)            &&  // writing all ones.
    (pmp_csr_rvfi_rdata.cfg[0] == '0)                    &&  // Related cfg is 0,
    (pmp_csr_rvfi_rdata.cfg[0+1] == '0)                  &&  // above cfg is 0.
    !rvfi_trap                                               // (Trap doesn't meddle.)
    |=>
    (rvfi_valid [->1])  ##0
    (rvfi_csr_pmpaddr_rdata[0][31:PMP_GRANULARITY] == '1)  &&
    (rvfi_csr_pmpaddr_rdata[0][PMP_GRANULARITY-1:0] == '0)
    // Note: _Can_ be generalized for all i
  );

  // Locking is forever
  for (genvar i = 0; i < PMP_NUM_REGIONS; i++) begin: gen_until_reset
    a_until_reset: assert property (
      pmp_csr_rvfi_rdata.cfg[i].lock  &&
      !pmp_csr_rvfi_rdata.mseccfg.rlb
      |->
      always pmp_csr_rvfi_rdata.cfg[i].lock
    );
  end

  // Locked entries, ignore pmpicfg/pmpaddri writes
  a_ignore_writes_notrap: assert property (
    is_rvfi_csr_write_instr  &&
    (rvfi_insn[31:20] inside {(CSRADDR_FIRST_PMPADDR + 0), (CSRADDR_FIRST_PMPCFG + 0)})  &&
    (pmp_csr_rvfi_rdata.cfg[0].lock && !pmp_csr_rvfi_rdata.mseccfg.rlb)  &&
    (rvfi_mode == MODE_M)
    |->
    (rvfi_trap.exception_cause != EXC_ILL_INSTR)
  );
  a_ignore_writes_nochange: assert property (
    rvfi_valid &&
    (pmp_csr_rvfi_rdata.cfg[0].lock && !pmp_csr_rvfi_rdata.mseccfg.rlb)
    |=>
    always (
      $stable(pmp_csr_rvfi_rdata.cfg[0])  &&
      $stable(pmp_csr_rvfi_rdata.addr[0])
    )
  );
/*
  a_not_ignore_writes_cfg: assert property (
    is_rvfi_csr_write_instr  &&
    (rvfi_insn[31:20] == (CSRADDR_FIRST_PMPCFG + 0))  &&
    ?
    |->
    ?
  );
*/
  property p_not_ignore_writes_cfg;
    logic [7:0] cfg;
    rvfi_valid  &&
    pmp_csr_rvfi_rdata.cfg[1].lock  &&
    (pmp_csr_rvfi_rdata.cfg[1].mode == PMP_MODE_TOR)  ##0
    (1, cfg = pmp_csr_rvfi_rdata.cfg[0])
    ##1
    (rvfi_valid [->1])  ##0
    (pmp_csr_rvfi_rdata.cfg[0] != cfg);
  endproperty : p_not_ignore_writes_cfg
  cov_not_ignore_writes_cfg: cover property (
    p_not_ignore_writes_cfg
    // TODO:silabs-robin  Write "a_not_ignore_writes_cfg".
  );
  // Note, can be easily checked for all i

  // Locked TOR, ignore i-1 addr writes
  for (genvar i = 1; i < PMP_NUM_REGIONS; i++) begin: gen_ignore_tor
    a_ignore_tor: assert property (
      rvfi_valid &&
      (pmp_csr_rvfi_rdata.cfg[i].lock && !pmp_csr_rvfi_rdata.mseccfg.rlb)  &&
      (pmp_csr_rvfi_rdata.cfg[i].mode == PMP_MODE_TOR)
      |=>
      always $stable(pmp_csr_rvfi_rdata.addr[i-1][31:PMP_GRANULARITY])
    );
  end

endmodule : uvmt_cv32e40s_pmprvfi_assert

`default_nettype wire
