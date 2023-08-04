//
// Copyright 2020 OpenHW Group
// Copyright 2022 Silicon Laboratories, Inc.
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

module uvmt_cv32e40s_clic_interrupt_assert
  import uvm_pkg::*;
  import cv32e40s_pkg::*;
  import uvma_rvfi_pkg::*;
  #(
    parameter int   CLIC            = 0,
    parameter int   CLIC_ID_WIDTH   = 5,
    parameter int   NUM_IRQ         = 32
  )(
    // gated clock
    input logic                       clk,
    // global clock
    input logic                       clk_i,
    input logic                       rst_ni,
    input logic                       fetch_enable,

    // interfaces
    uvmt_cv32e40s_support_logic_module_o_if_t.slave_mp  support_if,
    uvma_rvfi_instr_if_t                                rvfi_if,
    uvma_rvfi_csr_if_t                                  csr_mepc_if,
    uvma_rvfi_csr_if_t                                  csr_mcause_if,
    uvma_rvfi_csr_if_t                                  csr_mintthresh_if,
    uvma_rvfi_csr_if_t                                  csr_mintstatus_if,


    // CSR interface
    input logic [31:0]                dpc,
    input logic [31:0]                mintstatus,
    input logic [31:0]                mintthresh,
    input logic [31:0]                mstatus,
    input logic [31:0]                mtvec,
    input logic [31:0]                mtvt,
    input logic [31:0]                mepc,
    input logic [31:0]                mie,
    input logic [31:0]                mip,
    input logic [31:0]                mnxti,
    input logic [31:0]                mscratch,
    input logic [31:0]                mscratchcsw,
    input logic [31:0]                mscratchcswl,
    input logic [31:0]                dcsr,

    input logic [31:0]                rvfi_mepc_wdata,
    input logic [31:0]                rvfi_mepc_wmask,
    input logic [31:0]                rvfi_mepc_rdata,
    input logic [31:0]                rvfi_mepc_rmask,
    input logic [31:0]                rvfi_dpc_rdata,
    input logic [31:0]                rvfi_dpc_rmask,
    input logic [31:0]                rvfi_mscratch_wdata,
    input logic [31:0]                rvfi_mscratch_wmask,
    input logic [31:0]                rvfi_mscratch_rdata,
    input logic [31:0]                rvfi_mscratch_rmask,
    input logic [31:0]                rvfi_mcause_wmask,
    input logic [31:0]                rvfi_mcause_wdata,


    input logic [31:0]                mcause,

    input logic [31:0]                mtvec_addr_i,

    input logic [NUM_IRQ-1:0]         irq_i,
    input logic                       irq_ack,
    input logic [1:0]                 current_priv_mode,

    uvma_clic_if_t                    clic_if,

    input logic [CLIC_ID_WIDTH-1:0]   irq_id,
    input logic [7:0]                 irq_level,
    input logic [1:0]                 irq_priv,
    input logic                       irq_shv,

    input logic                       debug_mode,
    input logic                       debug_req,
    input logic                       debug_havereset,
    input logic                       debug_running,
    input logic [31:0]                debug_halt_addr,
    input logic [31:0]                debug_exc_addr,

    input logic                       obi_instr_req,
    input logic                       obi_instr_gnt,
    input logic                       obi_instr_rvalid,
    input logic                       obi_instr_rready,
    input logic [31:0]                obi_instr_addr,
    input logic [31:0]                obi_instr_rdata,
    input logic                       obi_instr_err,

    input logic                       obi_data_req,
    input logic                       obi_data_gnt,
    input logic                       obi_data_we,
    input logic [3:0]                 obi_data_be,
    input logic                       obi_data_rvalid,
    input logic                       obi_data_rready,
    input logic [31:0]                obi_data_addr,
    input logic [31:0]                obi_data_wdata,
    input logic                       obi_data_err,

    input logic [1:0]                 rvfi_mode,
    input logic [31:0]                rvfi_insn,
    input rvfi_intr_t                 rvfi_intr,
    input logic [31:0]                rvfi_rs1_rdata,
    input logic [31:0]                rvfi_rs2_rdata,
    input logic [31:0]                rvfi_rd_wdata,
    input logic                       rvfi_valid,
    input rvfi_trap_t                 rvfi_trap,
    input logic [31:0]                rvfi_pc_rdata,
    input logic [31:0]                rvfi_pc_wdata,
    input logic                       rvfi_dbg_mode,
    input logic [2:0]                 rvfi_dbg,

    input logic                       wu_wfe,
    input logic                       core_sleep_o
  );

  default clocking
    @(posedge clk_i);
  endclocking
  default disable iff !rst_ni;

  string info_tag = "CLIC_ASSERT";

  localparam logic [31:0] NMI_OFFSET    = 0;

  typedef struct packed {
    logic                       irq;
    logic [CLIC_ID_WIDTH-1:0]   id;
    logic [7:0]                 level;
    logic [1:0]                 priv;
    logic                       shv;
  } clic_irq_bundle_t;

  typedef struct packed {
    logic [CLIC_ID_WIDTH-1:0]   id;
    logic [7:0]                 level;
    logic [1:0]                 priv;
    logic                       shv;
  } internal_clic_irq_bundle_t;

  typedef struct packed {
    logic [31:24] mil;
    logic [23:16] reserved;
    logic [15:8]  sil;
    logic [7:0]   uil;
  } mintstatus_t;

  typedef struct packed {
    logic [31:8] reserved_0;
    logic [7:0]  th;
  } mintthresh_t;

  typedef struct packed {
    logic [31:31] sd;
    logic [30:23] reserved_3;
    logic [22:22] tsr;
    logic [21:21] tw;
    logic [20:20] tvm;
    logic [19:19] mxr;
    logic [18:18] sum;
    logic [17:17] mprv;
    logic [16:15] xs;
    logic [14:13] fs;
    logic [12:11] mpp;
    logic [10:9]  vs;
    logic [8:8]   spp;
    logic [7:7]   mpie;
    logic [6:6]   ube;
    logic [5:5]   spie;
    logic [4:4]   reserved_2;
    logic [3:3]   mie;
    logic [2:2]   reserved_1;
    logic [1:1]   sie;
    logic [0:0]   reserved_0;
  } mstatus_t;

  typedef struct packed {
    logic [31:7] base_31_7;
    logic [6:2]  base_6_2;
    logic [1:0]  mode;
  } mtvec_clic_t;

  localparam N_MTVT = 2+CLIC_ID_WIDTH > 6 ? 2+CLIC_ID_WIDTH : 6;

  typedef struct packed {
    logic [31:N_MTVT]  base_31_n;
    logic [N_MTVT-1:0] base_n_0;
  } mtvt_t;

  typedef struct packed {
    logic [31:1] m_exception_pc;
    logic [0:0]  reserved;
  } mepc_t;

  typedef enum logic [10:0] {
    INSTR_ACCESS_FAULT  = 11'd1,
    ILLEGAL_INSTR       = 11'd2,
    BREAKPOINT          = 11'd3,
    LOAD_ACCESS_FAULT   = 11'd5,
    STORE_ACCESS_FAULT  = 11'd7,
    ECALL_U_MODE        = 11'd8,
    ECALL_M_MODE        = 11'd11,
    INSTR_BUS_FAULT     = 11'd24,
    INSTR_PARITY_FAULT  = 11'd25,
    NMI_LOAD            = 11'd1024,
    NMI_STORE           = 11'd1025,
    NMI_LOAD_PARITY     = 11'd1026,
    NMI_STORE_PARITY    = 11'd1027
  } exccode_t;

  typedef struct packed {
    logic [31:31] interrupt;
    logic [30:30] minhv;
    logic [29:28] mpp;
    logic [27:27] mpie;
    logic [26:24] reserved_1;
    logic [23:16] mpil;
    logic [15:12] reserved_0;
    logic [11:11] exccode_11;
    union packed {
      logic [10:0]  exccode_10_0;
      exccode_t     exccode_val;
    }n;
  } mcause_t;

  typedef struct packed {
    logic [31:28] debugver;
    logic [27:18] reserved_27_18;
    logic [17:17] ebreakvs;
    logic [16:16] ebreakvu;
    logic [15:15] ebreakm;
    logic [14:14] reserved_14;
    logic [13:13] ebreaks;
    logic [12:12] ebreaku;
    logic [11:11] stepie;
    logic [10:10] stopcount;
    logic [9:9]   stoptime;
    logic [8:6]   cause;
    logic [5:5]   v;
    logic [4:4]   mprven;
    logic [3:3]   nmip;
    logic [2:2]   step;
    logic [1:0]   prv;
  } dcsr_t;

  typedef enum logic [1:0] {
    M_MODE = 2'b11,
    I_MODE = 2'b10, // Illegal, reserved
    S_MODE = 2'b01, // Not used in 40S/X
    U_MODE = 2'b00
  } priv_mode_t;

  typedef enum logic [2:0] {
    CSRRW = 3'b001,
    CSRRS = 3'b010,
    CSRRC = 3'b011,
    CSRRWI = 3'b101,
    CSRRSI = 3'b110,
    CSRRCI = 3'b111
  } csr_minor_opcode_t;

  typedef enum logic [6:0] {
    LOAD   = 7'b000_0011, LOAD_FP  = 7'b000_0111, CUS_0 = 7'b000_1011, MISC_MEM = 7'b000_1111, OP_IMM = 7'b001_0011, AUIPC = 7'b001_0111,OP_IMM_32 = 7'b001_1011,
    STORE  = 7'b010_0011, STORE_FP = 7'b010_0111, CUS_1 = 7'b010_1011, AMO      = 7'b010_1111, OP     = 7'b011_0011, LUI   = 7'b011_0111,OP_32     = 7'b011_1011,
    MADD   = 7'b100_0011, MSUB     = 7'b100_0111, NMSUB = 7'b100_1011, NMADD    = 7'b100_1111, OP_FP  = 7'b101_0011, RES_1 = 7'b101_0111,CUS_2     = 7'b101_1011,
    BRANCH = 7'b110_0011, JALR     = 7'b110_0111, RES_0 = 7'b110_1011, JAL      = 7'b110_1111, SYSTEM = 7'b111_0011, RES_2 = 7'b111_0111,CUS_3     = 7'b111_1011
  } major_opcode_t;

  typedef enum logic [2:0] {
    FUNCT3_LB  = 3'b000,
    FUNCT3_LH  = 3'b001,
    FUNCT3_LW  = 3'b010,
    FUNCT3_LBU = 3'b100,
    FUNCT3_LHU = 3'b101
  } load_size_e;

  typedef enum logic [2:0] {
    FUNCT3_SB = 3'b000,
    FUNCT3_SH = 3'b001,
    FUNCT3_SW = 3'b010
  } store_size_e;

  typedef enum logic [4:0] {
    X0  = 5'd0,
    X1  = 5'd1,
    X2  = 5'd2,
    X3  = 5'd3,
    X4  = 5'd4,
    X5  = 5'd5,
    X6  = 5'd6,
    X7  = 5'd7,
    X8  = 5'd8,
    X9  = 5'd9,
    X10 = 5'd10,
    X11 = 5'd11,
    X12 = 5'd12,
    X13 = 5'd13,
    X14 = 5'd14,
    X15 = 5'd15,
    X16 = 5'd16,
    X17 = 5'd17,
    X18 = 5'd18,
    X19 = 5'd19,
    X20 = 5'd20,
    X21 = 5'd21,
    X22 = 5'd22,
    X23 = 5'd23,
    X24 = 5'd24,
    X25 = 5'd25,
    X26 = 5'd26,
    X27 = 5'd27,
    X28 = 5'd28,
    X29 = 5'd29,
    X30 = 5'd30,
    X31 = 5'd31
  } gpr_t;

  typedef enum logic [31:20] {
    MSTATUS       = 12'h300,
    MISA          = 12'h301,
    MIE           = 12'h304,
    MTVEC         = 12'h305,
    MTVT          = 12'h307,
    MSTATUSH      = 12'h310,
    MCOUNTINHIBIT = 12'h320,
    MHPMEVENT3    = 12'h323,
    MHPMEVENT31   = 12'h33F,
    MSCRATCH      = 12'h340,
    MEPC          = 12'h341,
    MCAUSE        = 12'h342,
    MTVAL         = 12'h343,
    MIP           = 12'h344,
    MNXTI         = 12'h345,
    MINTSTATUS    = 12'h346,
    MINTTHRESH    = 12'h347,
    MSCRATCHCSW   = 12'h348,
    MSCRATCHCSWL  = 12'h349,
    MCLICBASE     = 12'h34A,
    TSELECT       = 12'h7A0,
    TDATA1        = 12'h7A1,
    TDATA2        = 12'h7A2,
    TDATA3        = 12'h7A3,
    TINFO         = 12'h7A4,
    TCONTROL      = 12'h7A5,
    DCSR          = 12'h7B0,
    DPC           = 12'h7B1,
    DSCRATCH0     = 12'h7B2,
    DSCRATCH1     = 12'h7B3
  } csr_name_t;

  typedef struct packed {
    csr_name_t           csr;
    union packed {
      gpr_t              rs1;
      logic [19:15]      uimm;
    }n;
    csr_minor_opcode_t funct3;
    gpr_t          rd;
    major_opcode_t opcode;
  } csr_instr_t;

  typedef struct packed {
    logic [31:12]  imm;
    gpr_t          rd;
  }u_type;

  typedef struct packed {
    logic [31:12]  imm;
    gpr_t          rd;
  }j_type;

  function logic[20:0] read_j_imm(logic[31:0] instr);
    automatic logic [20:0] imm;
    imm = instr >> 11;
    return { imm[20], imm[10:1], imm[11], imm[18:12], 1'b0 };
  endfunction : read_j_imm

  typedef struct packed {
    union packed {
      struct packed {
        logic [31:25]  funct7;
        gpr_t          rs2;
      }m;
      logic [31:20]  funct12;
    }n;
    gpr_t          rs1;
    logic [14:12]  funct3;
    gpr_t          rd;
  }r_type;

  typedef struct packed {
    gpr_t          rs3;
    logic [26:25]  funct2;
    gpr_t          rs2;
    gpr_t          rs1;
    logic [14:12]  funct3;
    gpr_t          rd;
  }r4_type;

  typedef struct packed {
    logic [31:20]  imm;
    gpr_t          rs1;
    logic [14:12]  funct3;
    gpr_t          rd;
  }i_type;

  typedef struct packed {
    logic [31:20]  imm;
    gpr_t          rs1;
    load_size_e    funct3;
    gpr_t          rd;
  }i_type_load;

  typedef struct packed {
    logic [31:25]  imm;
    gpr_t          rs2;
    gpr_t          rs1;
    logic [14:12]  funct3;
    gpr_t          rd;
  }b_type;

  function logic[11:0] read_b_imm(logic[31:0] instr);
    automatic logic [11:0] imm;
    imm = {instr[31], instr[7], instr[30:25], instr[11:8]};
    return imm;
  endfunction : read_b_imm

  typedef struct packed {
    logic [31:25]  imm_h;
    gpr_t          rs2;
    gpr_t          rs1;
    store_size_e   funct3;
    logic [11:7]   imm_l;
  }s_type;

  function logic[11:0] read_s_imm(logic[31:0] instr);
    automatic logic [11:0] imm;
    imm = {instr[31:25], instr[11:7]};
    return imm;
  endfunction : read_s_imm

  typedef struct packed {
    union packed {
      logic [31:7]       raw;
      i_type             i;
      i_type_load        i_load;
      j_type             j;
      s_type             s;
      r_type             r;
      r4_type            r4;
      b_type             b;
      u_type             u;
    }n;
    major_opcode_t opcode;
  } uncompressed_instr_t;

  // Instruction name enum, add instructions as needed
  typedef enum {
    FENCEI,
    MRET,
    DRET,
    ECALL,
    EBREAK,
    WFI,
    WFE,
    SB,
    SH,
    SW,
    LB,
    LH,
    LW,
    LBU,
    LHU,
    // Compressed
    CEBREAK,
    // Pseudo name, class of instruction
    STORE_INSN,
    LOAD_INSN
  } instr_names_e;

  logic core_not_in_debug;
  logic core_in_debug;
  logic is_csr_access_instr;

  logic [11:0] s_imm;
  logic [11:0] b_imm;
  logic [20:0] j_imm;
  logic [11:0] i_imm;

  uncompressed_instr_t mapped_instr;

  clic_irq_bundle_t clic;
  clic_irq_bundle_t clic_core;
  clic_irq_bundle_t clic_oic;

  csr_instr_t       csr_instr_raw;
  csr_instr_t       csr_instr;
  mintstatus_t      mintstatus_fields;
  mstatus_t         mstatus_fields;
  mtvec_clic_t      mtvec_fields;
  mtvt_t            mtvt_fields;
  mepc_t            mepc_fields;
  mcause_t          mcause_fields;
  mintthresh_t      mintthresh_fields;
  dcsr_t            dcsr_fields;


  mcause_t          rvfi_mcause_fields;
  mintstatus_t      rvfi_mintstatus_fields;

  logic is_mepc_access_instr;
  logic is_mtvec_access_instr;
  logic is_mtvt_access_instr;
  logic is_mcause_access_instr;
  logic is_mstatus_access_instr;
  logic is_mnxti_access_instr;
  logic is_mscratchcsw_access_instr;
  logic is_mscratchcswl_access_instr;
  logic is_csr_write;
  logic is_csr_read;
  logic is_mret_instr;
  logic is_fencei_instr;
  logic is_interrupt_allowed;
  logic is_dret_instr;
  logic is_wfi_instr;
  logic is_wfe_instr;

  logic is_load_instr;
  logic is_store_instr;

  logic is_valid_mnxti_write;
  logic is_valid_mnxti_read;

  logic is_load_bus_fault;
  logic is_store_bus_fault;
  logic is_load_parity_fault;
  logic is_store_parity_fault;
  logic is_instr_access_fault;
  logic is_instr_clicptr_fault;

  logic is_interrupt_taken;
  logic is_invalid_instr_word;
  logic is_cause_nmi;
  logic is_cause_interrupt;
  logic is_cause_instr_access_fault;
  logic is_cause_instr_bus_fault;
  logic is_trap_exception;
  logic is_intr_ecall_ebreak;
  logic is_intr_exception;

  logic is_wfe_wakeup_event;
  assign is_wfe_wakeup_event = wu_wfe;

  assign is_wfi_instr = is_instr(rvfi_insn, WFI);
  assign is_wfe_instr = is_instr(rvfi_insn, WFE);

  assign is_load_bus_fault           = (rvfi_intr.cause == NMI_LOAD           && rvfi_intr.intr == 1 && rvfi_intr.interrupt == 1);
  assign is_store_bus_fault          = (rvfi_intr.cause == NMI_STORE          && rvfi_intr.intr == 1 && rvfi_intr.interrupt == 1);
  assign is_load_parity_fault        = (rvfi_intr.cause == NMI_LOAD_PARITY    && rvfi_intr.intr == 1 && rvfi_intr.interrupt == 1);
  assign is_store_parity_fault       = (rvfi_intr.cause == NMI_STORE_PARITY   && rvfi_intr.intr == 1 && rvfi_intr.interrupt == 1);
  assign is_cause_instr_access_fault = (rvfi_intr.cause == INSTR_ACCESS_FAULT && rvfi_intr.intr == 1 && rvfi_intr.exception == 1);
  assign is_cause_instr_bus_fault    = (rvfi_intr.cause == INSTR_BUS_FAULT    && rvfi_intr.intr == 1 && rvfi_intr.exception == 1);
  assign is_cause_instr_parity_fault = (rvfi_intr.cause == INSTR_PARITY_FAULT && rvfi_intr.intr == 1 && rvfi_intr.exception == 1);

  assign is_cause_nmi                = (rvfi_intr.cause inside { NMI_LOAD, NMI_STORE, NMI_LOAD_PARITY, NMI_STORE_PARITY }) && rvfi_intr.intr && rvfi_intr.interrupt;
  assign is_cause_interrupt          = !(rvfi_intr.cause inside { NMI_LOAD, NMI_STORE, NMI_LOAD_PARITY, NMI_STORE_PARITY }) && rvfi_intr.intr && rvfi_intr.interrupt;

  assign is_interrupt_taken    = (rvfi_intr.intr == 1'b1 && rvfi_intr.interrupt == 1'b1);

  assign is_instr_access_fault = (rvfi_trap.exception_cause == INSTR_ACCESS_FAULT && rvfi_trap.exception == 1 && rvfi_trap.trap == 1);
  assign is_invalid_instr_word = ((   rvfi_trap.exception_cause == INSTR_ACCESS_FAULT
                                   || rvfi_trap.exception_cause == INSTR_BUS_FAULT
                                   || rvfi_trap.exception_cause == INSTR_PARITY_FAULT)
                                  && rvfi_trap.exception == 1'b1 && rvfi_trap.trap == 1'b1);

  assign is_instr_clicptr_fault = (rvfi_trap.exception_cause == INSTR_BUS_FAULT
                                  && rvfi_trap.clicptr  == 1'b1);

  assign is_trap_exception     = rvfi_trap.exception == 1'b1 && rvfi_trap.trap == 1'b1;
  assign is_intr_exception     = rvfi_intr.exception == 1'b1 && rvfi_intr.intr == 1'b1;
  assign is_intr_ecall_ebreak  = is_intr_exception
                                 && (rvfi_intr.cause == ECALL_M_MODE
                                  || rvfi_intr.cause == ECALL_U_MODE
                                  || rvfi_intr.cause == BREAKPOINT);


  assign s_imm = read_s_imm(rvfi_insn);
  assign b_imm = read_b_imm(rvfi_insn);
  assign j_imm = read_j_imm(rvfi_insn);
  assign i_imm = mapped_instr.n.i.imm;

  assign mapped_instr = uncompressed_instr_t'(rvfi_insn);

  // Map csrs to bitfield representations
  assign mintstatus_fields = mintstatus_t'(mintstatus);
  assign mintthresh_fields = mintthresh_t'(mintthresh);
  assign mstatus_fields    = mstatus_t'(mstatus);
  assign mtvec_fields      = mtvec_clic_t'(mtvec);
  assign mtvt_fields       = mtvt_t'(mtvt);
  assign mepc_fields       = mepc_t'(mepc);
  assign mcause_fields     = mcause_t'(mcause);
  assign dcsr_fields       = dcsr_t'(dcsr);

  assign rvfi_mcause_fields       = mcause_t'(csr_mcause_if.rvfi_csr_rdata);
  assign rvfi_mintstatus_fields   = mintstatus_t'(csr_mintstatus_if.rvfi_csr_rdata);

  always_comb begin
    clic.irq   = clic_if.clic_irq;
    clic.id    = clic_if.clic_irq_id;
    clic.level = clic_if.clic_irq_level;
    clic.priv  = clic_if.clic_irq_priv;
    clic.shv   = clic_if.clic_irq_shv;
  end

  always_comb begin
    if (!rst_ni) begin
      clic_core.id    = '0;
      clic_core.level = '0;
      clic_core.priv  = '0;
      clic_core.shv   = '0;
    end else begin
      clic_core.id    = irq_id;
      clic_core.level = irq_level;
      clic_core.priv  = irq_priv;
      clic_core.shv   = irq_shv;
    end
  end

  always @(posedge clk_i) begin
    if (!rst_ni) begin
      clic_core.irq <= 0;
    end else begin
      clic_core.irq <= clic.irq;
    end
  end


  assign core_not_in_debug            = debug_running;
  assign core_in_debug                = !core_not_in_debug;
  assign csr_instr_raw                = csr_instr_t'(rvfi_insn);
  assign is_csr_access_instr          = csr_instr_raw.opcode == SYSTEM
                                        && (csr_instr_raw.funct3 inside { CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI }) ;
  assign is_mnxti_access_instr        = is_csr_access_instr && rvfi_valid && csr_instr.csr == MNXTI;
  assign is_mepc_access_instr         = is_csr_access_instr && rvfi_valid && csr_instr.csr == MEPC;
  assign is_mtvec_access_instr        = is_csr_access_instr && rvfi_valid && csr_instr.csr == MTVEC;
  assign is_mtvt_access_instr         = is_csr_access_instr && rvfi_valid && csr_instr.csr == MTVT;
  assign is_mcause_access_instr       = is_csr_access_instr && rvfi_valid && csr_instr.csr == MCAUSE;
  assign is_mstatus_access_instr      = is_csr_access_instr && rvfi_valid && csr_instr.csr == MSTATUS;
  assign is_mscratchcsw_access_instr  = is_csr_access_instr && rvfi_valid && csr_instr.csr == MSCRATCHCSW;
  assign is_mscratchcswl_access_instr = is_csr_access_instr && rvfi_valid && csr_instr.csr == MSCRATCHCSWL;

  assign csr_instr = is_csr_access_instr ? csr_instr_raw : 32'h0000_0000;

  assign is_valid_mnxti_write = is_mnxti_access_instr && is_csr_write && rvfi_valid;
  assign is_valid_mnxti_read  = is_mnxti_access_instr && is_csr_read  && rvfi_valid;

  // TODO replace with non-poking signal
  assign is_interrupt_allowed = dut_wrap.cv32e40s_wrapper_i.core_i.controller_i.controller_fsm_i.interrupt_allowed;

  function logic fun_is_csr_write(csr_instr_t instr);
    if (instr.opcode == SYSTEM
      && (instr.funct3 inside { CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI })) begin

      case (instr.funct3)
        CSRRW, CSRRWI : fun_is_csr_write = 1'b1;
        CSRRS, CSRRC  : fun_is_csr_write = instr.n.rs1  ? 1'b1 : 1'b0;
        CSRRSI, CSRRCI: fun_is_csr_write = instr.n.uimm ? 1'b1 : 1'b0;

        // Should never be here
        default       : fun_is_csr_write = 1'b0;
      endcase
    end else begin
      fun_is_csr_write = 1'b0;
    end
  endfunction : fun_is_csr_write

  function logic fun_is_csr_read(csr_instr_t instr);
    if (instr.opcode == SYSTEM
      && (instr.funct3 inside { CSRRW, CSRRS, CSRRC, CSRRWI, CSRRSI, CSRRCI })) begin
      case (instr.funct3)
        CSRRW, CSRRWI : fun_is_csr_read  = instr.rd ? 1'b1 : 1'b0;
        CSRRS, CSRRC  : fun_is_csr_read  = 1'b1;
        CSRRSI, CSRRCI: fun_is_csr_read  = 1'b1;

        // Should never be here
        default       : fun_is_csr_read  = 1'b0;
      endcase
    end else begin
      fun_is_csr_read = 1'b0;
    end
  endfunction : fun_is_csr_read

  always_comb begin
    if (is_csr_access_instr) begin
      is_csr_write = fun_is_csr_write(csr_instr);
      is_csr_read  = fun_is_csr_read(csr_instr);
    end else begin
      is_csr_write = 0;
      is_csr_read  = 0;
    end
  end


  function is_instr(uncompressed_instr_t instr, instr_names_e instr_type);
    if (is_invalid_instr_word) begin
      return 1'b0;
    end

    case (instr_type)
      FENCEI : return (   (instr.opcode         == MISC_MEM)
                       && (instr.n.i.rd         == 5'b0_0000)
                       && (instr.n.i.funct3     == 3'b001)
                       && (instr.n.i.rs1        == 5'b0_0000)
                       && (instr.n.i.imm        == 12'h000));
      ECALL  : return (   (instr.opcode         == SYSTEM)
                       && (instr.n.i.imm        == 12'b0000_0000_0000));
      EBREAK : return (   (instr.opcode         == SYSTEM)
                       && (instr.n.i.imm        == 12'b0000_0000_0001));
      CEBREAK: return (   (instr                == 32'b0000_0000_1001_0010)); // compressed
      MRET   : return (   (instr.opcode         == SYSTEM)
                       && (instr.n.r.rd         == 5'b0_0000)
                       && (instr.n.r.n.m.funct7 == 12'b001_1000)
                       && (instr.n.r.n.m.rs2    == 5'b0_0010)
                       && (instr.n.r.rs1        == 5'b0_0000)
                       && (instr.n.r.funct3     == 3'b000));
      DRET   : return (   (instr.opcode         == SYSTEM)
                       && (instr.n.r.n.funct12  == 12'b0111_1011_0010));
      WFI    : return (   (instr.opcode         == SYSTEM)
                       && (instr.n.r.rd         == 5'b0_0000)
                       && (instr.n.r.funct3     == 3'b000)
                       && (instr.n.r.rs1        == 5'b0_0000)
                       && (instr.n.r.n.funct12  == 12'b0001_0000_0101));
      WFE    : return (   (instr.opcode         == SYSTEM)
                       && (instr.n.r.rd         == 5'b0_0000)
                       && (instr.n.r.funct3     == 3'b000)
                       && (instr.n.r.rs1        == 5'b0_0000)
                       && (instr.n.r.n.funct12  == 12'b1000_1100_0000));
      SB     : return (   (instr.opcode         == STORE)
                       && (instr.n.s.funct3     == FUNCT3_SB));
      SH     : return (   (instr.opcode         == STORE)
                       && (instr.n.s.funct3     == FUNCT3_SH));
      SW     : return (   (instr.opcode         == STORE)
                       && (instr.n.s.funct3     == FUNCT3_SW));
      STORE_INSN : return (instr.opcode         == STORE)
                       && (instr.n.s.funct3 inside { FUNCT3_SB, FUNCT3_SH, FUNCT3_SW });
      LB     : return (   (instr.opcode         == LOAD)
                       && (instr.n.i.funct3     == FUNCT3_LB));
      LH     : return (   (instr.opcode         == LOAD)
                       && (instr.n.i.funct3     == FUNCT3_LH));
      LW     : return (   (instr.opcode         == LOAD)
                       && (instr.n.i.funct3     == FUNCT3_LW));
      LBU    : return (   (instr.opcode         == LOAD)
                       && (instr.n.i.funct3     == FUNCT3_LBU));
      LHU    : return (   (instr.opcode         == LOAD)
                       && (instr.n.i.funct3     == FUNCT3_LHU));
      LOAD_INSN  : return (instr.opcode         == LOAD)
                       && (instr.n.i.funct3 inside { FUNCT3_LB, FUNCT3_LH, FUNCT3_LW, FUNCT3_LBU, FUNCT3_LHU });
    endcase
  endfunction : is_instr

  assign is_mret_instr   = rvfi_valid && is_instr(rvfi_insn, MRET);
  assign is_dret_instr   = rvfi_valid && is_instr(rvfi_insn, DRET);
  assign is_fencei_instr = rvfi_valid && is_instr(rvfi_insn, FENCEI);

  assign is_store_instr  = rvfi_valid && is_instr(rvfi_insn, STORE_INSN);
  assign is_load_instr   = rvfi_valid && is_instr(rvfi_insn, LOAD_INSN);

  function logic is_store_instr_addr_in_mtvt_region(uncompressed_instr_t instr);
    automatic logic [31:0] base   = 0;
    automatic logic [11:0] offset = 0;
    case (is_instr(instr, STORE_INSN))
      1: offset = s_imm;
      0: return 1'b0;
    endcase
    base = rvfi_rs1_rdata;
    return base + offset inside { [mtvt : mtvt + ((2**CLIC_ID_WIDTH * 4))] } ? 1'b1 : 1'b0;
  endfunction : is_store_instr_addr_in_mtvt_region

  function logic is_load_instr_addr_in_mtvt_region(uncompressed_instr_t instr);
    automatic logic [31:0] base = 0;
    automatic logic [11:0] offset = 0;
    case (is_instr(instr, LOAD_INSN))
      1: offset = i_imm;
      0: return 1'b0;
    endcase
    base = rvfi_rs1_rdata;
    return base + offset inside { [mtvt : mtvt + ((2**CLIC_ID_WIDTH * 4))] } ? 1'b1 : 1'b0;
  endfunction : is_load_instr_addr_in_mtvt_region

  generate
  if (CLIC) begin : gen_clic_assertions

    // ------------------------------------------------------------------------
    // mintstatus.mil resets to 0
    // ------------------------------------------------------------------------

    property p_mintstatus_mil_reset_to_zero;
      $rose(rst_ni) |-> mintstatus_fields.mil == 8'h0;
    endproperty : p_mintstatus_mil_reset_to_zero

    a_mintstatus_mil_reset_to_zero: assert property (p_mintstatus_mil_reset_to_zero)
    else
      `uvm_error(info_tag,
        $sformatf("mintstatus.mil non-zero reset value not allowed"));

    // ------------------------------------------------------------------------
    // mstatus.mie should reset to zero
    // ------------------------------------------------------------------------

    property p_mstatus_mie_reset_to_zero;
      $rose(rst_ni) |-> mstatus_fields.mie == 1'b0;
    endproperty : p_mstatus_mie_reset_to_zero

    a_mstatus_mie_reset_to_zero: assert property (p_mstatus_mie_reset_to_zero)
    else
      `uvm_error(info_tag,
        $sformatf("mstatus.mie non-zero reset value not allowed"));

    // ------------------------------------------------------------------------
    // mtvec reset value is correct
    // ------------------------------------------------------------------------

    property p_mtvec_reset_value_correct;
      $rose(fetch_enable) |=> ##1
        mtvec_fields.base_31_7 == mtvec_addr_i[31:7] &&
        mtvec_fields.base_6_2  == 5'h00 &&
        mtvec_fields.mode      == M_MODE;
    endproperty : p_mtvec_reset_value_correct;

    a_mtvec_reset_value_correct: assert property (p_mtvec_reset_value_correct)
    else
      `uvm_error(info_tag,
        $sformatf("mtvec reset value: 0x%08h, should have been 0x%08h",
          mtvec_fields, mtvec_addr_i));

    // ------------------------------------------------------------------------
    // clic.priv should always be machine mode
    // ------------------------------------------------------------------------

    property p_clic_mode_only;
      clic.priv == M_MODE;
    endproperty : p_clic_mode_only

    a_clic_mode_only: assert property (p_clic_mode_only)
    else
      `uvm_error(info_tag,
        $sformatf("When clic is enabled, it should be the ONLY mode available"));

    // ------------------------------------------------------------------------
    // NMI address should be at the fifthteenth entry in the mtvec table
    // ------------------------------------------------------------------------

    property p_nmi_to_mtvec_offset;
            is_cause_nmi
         && rvfi_valid
      |->
            rvfi_pc_rdata == ({$past(mtvec_fields.base_31_7), $past(mtvec_fields.base_6_2), 2'b00} + NMI_OFFSET)
      or
            rvfi_pc_rdata == ({$past(mtvec_fields.base_31_7), $past(mtvec_fields.base_6_2), 2'b00} + NMI_OFFSET + 2)
         && (mapped_instr.opcode[1:0] != 2'b11)
      or
            is_dret_instr
        ##1 rvfi_valid[->1]
        ##0 rvfi_pc_rdata == ({$past(mtvec_fields.base_31_7), $past(mtvec_fields.base_6_2), 2'b00} + NMI_OFFSET)
         && !rvfi_dbg_mode
      or
        //    rvfi_valid[->1]
        ##0 rvfi_pc_rdata == debug_halt_addr
         && rvfi_dbg_mode
      ;
    endproperty : p_nmi_to_mtvec_offset

    a_nmi_to_mtvec_offset: assert property (p_nmi_to_mtvec_offset)
    else
      `uvm_error(info_tag,
        $sformatf("Taken nmi address wrong"));

    // ------------------------------------------------------------------------
    // CLIC_ID_WIDTH setting should be for 1-1024 interrupts
    // ------------------------------------------------------------------------

    property p_clic_valid_setting;
      CLIC_ID_WIDTH inside {[1:10]};
    endproperty : p_clic_valid_setting

    a_clic_valid_setting: assert property (p_clic_valid_setting)
    else
      `uvm_error(info_tag,
        $sformatf("CLIC_ID_WIDTH is invalid, is %0d, should be in range 1 .. 10",
                  CLIC_ID_WIDTH));

    // ------------------------------------------------------------------------
    // irq_i[0:31] should be hardcoded zero
    // ------------------------------------------------------------------------

    for (genvar i = 0; i < NUM_IRQ; i++) begin : gen_non_clic_tieoff

      property p_tieoff_zero_irq_i;
        irq_i[i] == '0;
      endproperty : p_tieoff_zero_irq_i;

      a_tieoff_zero_irq_i : assert property (p_tieoff_zero_irq_i)
      else
        `uvm_error(info_tag,
           $sformatf("irq_i[%0d] should be zero, is %0b",
             i,
             irq_i[i])
        );
    end

    // ------------------------------------------------------------------------
    // Enabled and pending interrupts should eventually be taken,
    // assuming that the request is not retracted
    // ------------------------------------------------------------------------

    localparam MAX_STALL_CYCLES = 20;

    property p_obi_instr_max_load_stalls;
      $stable(obi_instr_fifo_tag_waddr) && (obi_instr_fifo_tag_waddr != '0)
      |->
      ($stable(obi_instr_fifo_tag_waddr))[*0:MAX_STALL_CYCLES]
      ##1 $changed(obi_instr_fifo_tag_waddr);
    endproperty : p_obi_instr_max_load_stalls

    property p_obi_instr_max_gnt_stalls;
      obi_instr_pending
      |->
      obi_instr_pending[*0:MAX_STALL_CYCLES] ##1 obi_instr_push;
    endproperty : p_obi_instr_max_gnt_stalls

    property p_obi_data_max_load_stalls;
      $stable(obi_data_fifo_tag_waddr) && (obi_data_fifo_tag_waddr != '0)
      |->
      ($stable(obi_data_fifo_tag_waddr))[*0:MAX_STALL_CYCLES]
      ##1 $changed(obi_data_fifo_tag_waddr);
    endproperty : p_obi_data_max_load_stalls

    property p_obi_data_max_gnt_stalls;
      obi_data_pending
      |->
      obi_data_pending[*0:MAX_STALL_CYCLES] ##1 obi_data_push;
    endproperty : p_obi_data_max_gnt_stalls

    localparam MAX_RVFI_VALID_DELAY = 64;

    property p_instr_valid_delay;
        !rvfi_valid |-> !rvfi_valid[*0:MAX_RVFI_VALID_DELAY] ##1 rvfi_valid;
    endproperty

    // TODO: disabled pending discussions on if & how to do this
    //// Pending and enabled interrupts will eventually be taken if the conditions are right
    //// Excludes checking in blocking regions (debug, exception handlers, nmi)
    //// Deliberately written as a liveness property, might want to exclude or constrain
    //// for sim to avoid the liveness issues.
    ////sequence s_irq_ack;
    ////  irq_ack within 1[*1:$];
    ////endsequence : s_irq_ack

    //property p_always_taken;
    //  @(posedge clk_i)

    //  disable iff(
    //       !rst_ni
    //    || core_in_debug
    //    || rvfi_intr.exception
    //    || rvfi_trap.exception
    //    || is_cause_nmi
    //    || $changed(mstatus_fields.mie, @(posedge clk_i))
    //    || $changed(mintthresh_fields.th, @(posedge clk_i))
    //    || $changed(mintstatus_fields.mil, @(posedge clk_i))
    //            )
    //  // Valid pending, clic stable and no outstanding obi data transactions
    //  (seq_irq_pend(1'b1) and $stable(clic) ) ##1 is_interrupt_allowed
    //  |->
    //   irq_ack
    //  ;
    //endproperty : p_always_taken

    //a_always_taken: assert property(p_always_taken)
    //else
    //  `uvm_error(info_tag,
    //    $sformatf("Interrupt should have been taken"));

    // ------------------------------------------------------------------------
    // irq_ack is always single cycle pulse
    // ------------------------------------------------------------------------

    property p_irq_ack_is_always_single_cycle_pulse;
        irq_ack
      |=>
        !irq_ack;
    endproperty : p_irq_ack_is_always_single_cycle_pulse

    a_irq_ack_is_always_single_cycle_pulse: assert property (p_irq_ack_is_always_single_cycle_pulse)
    else
      `uvm_error(info_tag,
        $sformatf("irq_ack not single cycle pulse"));

    // ------------------------------------------------------------------------
    // irq_ack should only be asserted on taken interrupts
    // ------------------------------------------------------------------------

    logic [7:0] effective_clic_level;

    always_comb begin
      effective_clic_level = mintthresh_fields.th > mintstatus_fields.mil ? mintthresh_fields.th : mintstatus_fields.mil;
    end

    sequence seq_irq_pend(bit ok = 1'b1);
      @(posedge clk_i)

      // valid pending
      ok ##0 (
            (mstatus_fields.mie
         && $past(clic.irq)
         && $past(clic.priv) == current_priv_mode
         && $past(clic.level) > effective_clic_level)
        or
            ($past(clic.irq)
         && $past(clic.priv) > current_priv_mode
         && $past(clic.level) > 0)
        )
      or
      // no valid pending
      !ok ##0 (
            !(mstatus_fields.mie
         && $past(clic.irq)
         && $past(clic.priv) == current_priv_mode
         && $past(clic.level) > effective_clic_level)
        and
            !($past(clic.irq)
         && $past(clic.priv) > current_priv_mode
         && $past(clic.level) > 0)
      )
      ;
    endsequence : seq_irq_pend

    property p_irq_ack_valid;
        irq_ack
      |->
        seq_irq_pend(1'b1)
      ;
    endproperty : p_irq_ack_valid

    a_irq_ack_valid: assert property (p_irq_ack_valid)
    else
      `uvm_error(info_tag,
        $sformatf("irq ack prerequisites not met and ack occurred"));

    // ------------------------------------------------------------------------
    // There should be no irq_ack unless there was a pending and enabled irq
    // ------------------------------------------------------------------------
    property p_no_irq_no_ack;
          // Never irq_ack unless we had a valid and pending interrupt present.
          seq_irq_pend(1'b0).triggered
      |->
          !irq_ack
      ;
    endproperty : p_no_irq_no_ack

    a_no_irq_no_ack : assert property (p_no_irq_no_ack)
    else
      `uvm_error(info_tag,
        $sformatf("irq ack prerequisites not met and ack occurred"));

    // ------------------------------------------------------------------------
    // There should be no irq_ack on taken nmi
    //
    // Ideally would like to have an assertion for this case, but it is not
    // possible to separate cases on rvfi where the taken interrupts handler
    // is interrupted by nmi, and thus appears to have an ack caused by nmi
    //
    // The remaining cases will be covered by no irq_ack without valid,
    // pending irq, and that ack always occurs together with a valid pending
    // interrupt condition.
    // ------------------------------------------------------------------------

    // ------------------------------------------------------------------------
    // Every irq_ack should be followed by an rvfi_intr
    // ------------------------------------------------------------------------

    property p_every_ack_followed_by_rvfi_intr;
            irq_ack
        ##1 rvfi_valid[->1]
      |->
            // all the following are rvfi_intr-based signals.
            is_cause_interrupt
      or
            is_cause_nmi
      or
            is_cause_instr_access_fault
      or
            is_cause_instr_bus_fault
      or
            is_cause_instr_parity_fault
      ;
    endproperty : p_every_ack_followed_by_rvfi_intr

    a_every_ack_followed_by_rvfi_intr: assert property (p_every_ack_followed_by_rvfi_intr)
    else
      `uvm_error(info_tag,
        $sformatf("Every irq_ack should be followed by the corresponding rvfi_intr"));

    // ------------------------------------------------------------------------
    // mie is unused, and should be hard coded zero
    // ------------------------------------------------------------------------

    property p_mie_unused_hardcode_zero;
      mie == 32'h0000_0000;
    endproperty : p_mie_unused_hardcode_zero

    a_mie_unused_hardcode_zero: assert property (p_mie_unused_hardcode_zero)
    else
      `uvm_error(info_tag,
        $sformatf("Mie is unused and should always read zero"));

    // ------------------------------------------------------------------------
    // mip is unused, and should be hard coded zero
    // ------------------------------------------------------------------------

    property p_mip_unused_hardcode_zero;
      mip == 32'h0000_0000;
    endproperty : p_mip_unused_hardcode_zero

    a_mip_unused_hardcode_zero: assert property (p_mip_unused_hardcode_zero)
    else
      `uvm_error(info_tag,
        $sformatf("Mip is unused and should always read zero"));

    // ------------------------------------------------------------------------
    // mtvec should always be aligned to 128 bytes
    // ------------------------------------------------------------------------

    property p_mtvec_aligned_to_128_bytes;
      mtvec_fields.base_6_2 == 5'b0_0000;
    endproperty : p_mtvec_aligned_to_128_bytes;

    a_mtvec_aligned_to_128_bytes: assert property (p_mtvec_aligned_to_128_bytes)
    else
      `uvm_error(info_tag,
         $sformatf("mtvec[6:2] should have been zero (128 bytes alignment), was %05b",
           mtvec_fields.base_6_2));

    // ------------------------------------------------------------------------
    // mtvec.mode should always be clic mode
    // ------------------------------------------------------------------------

    property p_mtvec_mode_always_clic;
      mtvec_fields.mode == 2'b11;
    endproperty : p_mtvec_mode_always_clic

    a_mtvec_mode_always_clic: assert property (p_mtvec_mode_always_clic)
    else
      `uvm_error(info_tag,
        $sformatf("mtvec.mode should always be clic in clic mode, is %02b",
          mtvec_fields.mode));

    // ------------------------------------------------------------------------
    // fencei guarantees that updated mtvt table values are fetched
    // ------------------------------------------------------------------------

    //arbitrary limit, 8 should be OK for now (by some margin) update as needed
    localparam MAX_OBI_OUTSTANDING = 8;
    logic [31:0] mtvt_write_offset;
    logic [31:0] mtvt_read_offset;
    logic [31:0] mtvt_table_value[0:(2**(CLIC_ID_WIDTH))-1];
    logic is_mtvt_store_event;
    logic no_mtvt_store_event_occurred;
    int   items_in_obi_instr_fifo;
    int   items_in_obi_data_wfifo;
    logic obi_instr_pop;
    logic obi_instr_push;
    logic obi_instr_pending;
    logic obi_data_pop;
    logic obi_data_push;
    logic obi_data_pending;
    logic [0:8][31:0] obi_instr_addr_fifo;
    logic [0:8][31:0] obi_data_addr_fifo;
    logic [31:0] obi_instr_resp;

    logic [2:0] obi_instr_service;
    logic [2:0] obi_instr_service_n;
    logic [2:0] obi_instr_request;
    logic [2:0] obi_instr_request_n;
    logic [2:0] obi_data_service;
    logic [2:0] obi_data_service_n;
    logic [2:0] obi_data_request;
    logic [2:0] obi_data_request_n;

    always @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        obi_instr_service <= '0;
        obi_instr_request <= '0;
        obi_data_service  <= '0;
        obi_data_request  <= '0;
      end else begin
        obi_instr_request <= obi_instr_request_n;
        obi_instr_service <= obi_instr_service_n;
        obi_data_request  <= obi_data_request_n;
        obi_data_service  <= obi_data_service_n;
      end
    end

    always_comb begin
      //if (!rst_ni) begin
      //  obi_instr_request_n <= '0;
      //  obi_instr_service_n <= '0;
      //  obi_data_request_n  <= '0;
      //  obi_data_service_n  <= '0;
      //end else begin
        if (obi_instr_push) begin
          obi_instr_request_n <= obi_instr_request == 3'd7 ? obi_instr_request + 3'd2 : obi_instr_request + 3'd1;
        end else begin
          obi_instr_request_n <= obi_instr_request;
        end

        if (obi_instr_pop) begin
          obi_instr_service_n <= obi_instr_service == 3'd7 ? obi_instr_service + 3'd2 : obi_instr_service + 3'd1;
        end else begin
          obi_instr_service_n <= obi_instr_service;
        end

        if (obi_data_push) begin
          obi_data_request_n <= obi_data_request == 3'd7 ? obi_data_request + 3'd2 : obi_data_request + 3'd1;
        end else begin
          obi_data_request_n <= obi_data_request;
        end

        if (obi_data_pop) begin
          obi_data_service_n <= obi_data_service == 3'd7 ? obi_data_service + 3'd2 : obi_data_service + 3'd1;
        end else begin
          obi_data_service_n <= obi_data_service;
        end
      //end
    end

    // New obi_instr read request
    assign obi_instr_push = obi_instr_req && obi_instr_gnt;
    // New obi_instr read fulfillment
    assign obi_instr_pop  = obi_instr_rvalid && obi_instr_rready;

    // New obi_data read request
    assign obi_data_push = obi_data_req && obi_data_gnt;
    // New obi_data read fulfillment
    assign obi_data_pop  = obi_data_rvalid && obi_data_rready;

    assign obi_instr_pending = obi_instr_req && !obi_instr_gnt;
    assign obi_data_pending = obi_data_req && !obi_data_gnt;

    logic is_read_mtvt_table_val_obi;
    localparam logic [31:0] mtvt_max_offset = ((2**CLIC_ID_WIDTH)*4-1);

    always_comb begin
      if (!rst_ni) begin
        is_read_mtvt_table_val_obi <= 1'b0;
      end
      else begin
        is_read_mtvt_table_val_obi <= (obi_instr_addr inside { [mtvt:mtvt+mtvt_max_offset ]}) && obi_instr_req && obi_instr_gnt;
      end
    end

    logic is_write_mtvt_table_val_obi;
    always_comb begin
      if (!rst_ni) begin
        is_write_mtvt_table_val_obi <= 1'b0;
      end
      else begin
        is_write_mtvt_table_val_obi <= (obi_data_addr inside { [mtvt:mtvt+mtvt_max_offset ]}) && obi_data_req && obi_data_gnt && obi_data_we;
      end
    end

    logic [31:0] last_mtvt_table_read_addr;
    always @(posedge clk_i) begin
      if (!rst_ni) begin
        last_mtvt_table_read_addr <= 0;
      end else begin
        if ($fell(is_read_mtvt_table_val_obi)) begin
          last_mtvt_table_read_addr <= $past(obi_instr_addr);
        end else begin
          last_mtvt_table_read_addr <= last_mtvt_table_read_addr;
        end
      end
    end

    logic is_mtvt_load_event;
    assign is_mtvt_store_event = is_store_instr_addr_in_mtvt_region(rvfi_insn) && !rvfi_trap.exception && rvfi_valid;
    assign is_mtvt_load_event  = is_read_mtvt_table_val_obi;

    always@* begin
      if (!rst_ni) begin
        no_mtvt_store_event_occurred <= 1'b1;
        `ifndef FORMAL
        // We don't want this table to be initialized in formal, should be free net for formal
        mtvt_table_value <= {<<{ '0}};
        `endif
      end
      if (is_mtvt_store_event) begin
        mtvt_write_offset                       <= rvfi_rs1_rdata + s_imm - mtvt;
        mtvt_table_value[(CLIC_ID_WIDTH)'(mtvt_write_offset/'d4)] <= rvfi_rs2_rdata;
        no_mtvt_store_event_occurred <= 0;
      end
      else if (no_mtvt_store_event_occurred && is_mtvt_load_event) begin
        mtvt_read_offset <= rvfi_rs1_rdata + i_imm - mtvt;
        mtvt_table_value[(CLIC_ID_WIDTH)'(mtvt_read_offset/'d4)] <= rvfi_rd_wdata;
      end
    end

    sequence s_store_mtvt_value;
      @(posedge clk_i)

      is_mtvt_store_event;
    endsequence : s_store_mtvt_value

    // TODO cleanup names
    logic [0:7][3:0] obi_instr_fifo_tag;
    logic [0:7][3:0] obi_instr_fifo_tag_n;
    logic [2:0]      obi_instr_fifo_tag_size;
    logic [2:0]      obi_instr_fifo_tag_size_n;
    logic [0:7][3:0] obi_data_fifo_tag;
    logic [0:7][3:0] obi_data_fifo_tag_n;
    logic [2:0]      obi_data_fifo_tag_size;
    logic [2:0]      obi_data_fifo_tag_size_n;

    logic is_mtvt_table_access;
    logic is_read_from_mtvt;
    logic [0:7][3:0]  obi_instr_tag;
    logic [0:7][3:0]  obi_instr_tag_n;
    logic [0:7][31:0] obi_instr_tag_addr;
    logic [0:7][31:0] obi_instr_tag_addr_n;
    logic [2:0]       obi_instr_tag_size;
    logic [2:0]       obi_instr_tag_size_n;

    assign is_mtvt_table_access = obi_instr_addr inside { [mtvt : mtvt + ((2**CLIC_ID_WIDTH)*4)-1] } && obi_instr_push;
    assign is_read_from_mtvt = obi_instr_fifo_tag_out.addr inside { [ mtvt : mtvt + ((2**CLIC_ID_WIDTH)*4)-1 ] } && obi_instr_pop;

    typedef struct packed {
      logic [35:32] tag;
      logic [31:0]  addr;
    } obi_tagged_txn_t;

    logic obi_instr_fifo_tag_we;
    logic obi_instr_fifo_tag_re;
    logic obi_instr_fifo_tag_full;
    logic obi_instr_fifo_tag_empty;
    logic [7:0] obi_instr_fifo_tag_wena;
    logic [7:0] obi_instr_fifo_tag_rena;
    logic [2:0] obi_instr_fifo_tag_waddr;
    logic [2:0] obi_instr_fifo_tag_waddr_ff;
    logic [2:0] obi_instr_fifo_tag_raddr;
    logic [2:0] obi_instr_fifo_tag_raddr_ff;
    obi_tagged_txn_t obi_instr_fifo_tag_ff[8];
    obi_tagged_txn_t obi_instr_fifo_tag_out;

    logic obi_data_fifo_tag_we;
    logic obi_data_fifo_tag_re;
    logic obi_data_fifo_tag_full;
    logic obi_data_fifo_tag_empty;
    logic [7:0] obi_data_fifo_tag_wena;
    logic [7:0] obi_data_fifo_tag_rena;
    logic [2:0] obi_data_fifo_tag_waddr;
    logic [2:0] obi_data_fifo_tag_waddr_ff;
    logic [2:0] obi_data_fifo_tag_raddr;
    logic [2:0] obi_data_fifo_tag_raddr_ff;
    obi_tagged_txn_t obi_data_fifo_tag_ff[8];
    obi_tagged_txn_t obi_data_fifo_tag_out;

    assign obi_instr_fifo_tag_wena = obi_instr_fifo_tag_we ? ( 8'h1 << obi_instr_fifo_tag_waddr ) : 8'h00;
    assign obi_instr_fifo_tag_rena = obi_instr_fifo_tag_re ? ( 8'h1 << obi_instr_fifo_tag_raddr ) : 8'h00;

    assign obi_data_fifo_tag_wena = obi_data_fifo_tag_we ? ( 8'h1 << obi_data_fifo_tag_waddr ) : 8'h00;
    assign obi_data_fifo_tag_rena = obi_data_fifo_tag_re ? ( 8'h1 << obi_data_fifo_tag_raddr ) : 8'h00;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        obi_instr_fifo_tag_waddr_ff <= 0;
        obi_data_fifo_tag_waddr_ff  <= 0;
        obi_instr_fifo_tag_raddr_ff <= 0;
        obi_data_fifo_tag_raddr_ff  <= 0;
        obi_instr_fifo_tag_waddr <= 0;
        obi_data_fifo_tag_waddr  <= 0;
        obi_instr_fifo_tag_raddr <= 0;
        obi_data_fifo_tag_raddr  <= 0;
      end else begin

        if (obi_instr_fifo_tag_we) begin
          obi_instr_fifo_tag_waddr <= obi_instr_fifo_tag_waddr < 3'd7 ? obi_instr_fifo_tag_waddr + 3'd1 : obi_instr_fifo_tag_waddr + 3'd2;
        end else begin
          obi_instr_fifo_tag_waddr <= obi_instr_fifo_tag_waddr;
        end

        if (obi_data_fifo_tag_we) begin
          obi_data_fifo_tag_waddr <= obi_data_fifo_tag_waddr < 3'd7 ? obi_data_fifo_tag_waddr + 3'd1 : obi_data_fifo_tag_waddr + 3'd2;
        end else begin
          obi_data_fifo_tag_waddr <= obi_data_fifo_tag_waddr;
        end

        if (obi_instr_fifo_tag_re) begin
          obi_instr_fifo_tag_raddr <= obi_instr_fifo_tag_raddr < 3'd7 ? obi_instr_fifo_tag_raddr + 3'd1 : obi_instr_fifo_tag_raddr + 3'd2;
        end else begin
          obi_instr_fifo_tag_raddr <= obi_instr_fifo_tag_raddr;
        end

        if (obi_data_fifo_tag_re) begin
          obi_data_fifo_tag_raddr <= obi_data_fifo_tag_raddr < 3'd7 ? obi_data_fifo_tag_raddr + 3'd1 : obi_data_fifo_tag_raddr + 3'd2;
        end else begin
          obi_data_fifo_tag_raddr <= obi_data_fifo_tag_raddr;
        end

        // obi instr fifo write
        if (obi_instr_fifo_tag_we) begin
          obi_instr_fifo_tag_waddr_ff <= obi_instr_fifo_tag_waddr;
        end else begin
          obi_instr_fifo_tag_waddr_ff <= obi_instr_fifo_tag_waddr_ff;
        end
        // obi instr fifo read
        if (obi_instr_fifo_tag_re) begin
          obi_instr_fifo_tag_raddr_ff <= obi_instr_fifo_tag_raddr;
        end else begin
          obi_instr_fifo_tag_raddr_ff <= obi_instr_fifo_tag_raddr_ff;
        end

        // obi data fifo write
        if (obi_data_fifo_tag_we) begin
          obi_data_fifo_tag_waddr_ff <= obi_data_fifo_tag_waddr;
        end else begin
          obi_data_fifo_tag_waddr_ff <= obi_data_fifo_tag_waddr_ff;
        end
        // obi data fifo read
        if (obi_data_fifo_tag_re) begin
          obi_data_fifo_tag_raddr_ff <= obi_data_fifo_tag_raddr;
        end else begin
          obi_data_fifo_tag_raddr_ff <= obi_data_fifo_tag_raddr_ff;
        end
      end
    end

    for (genvar i = 0; i < 8; i++) begin
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          obi_instr_fifo_tag_ff[i] <= '0;
        end else begin
          if (obi_instr_fifo_tag_wena[i]) begin
            obi_instr_fifo_tag_ff[i].tag  <= obi_instr_request_n;
            obi_instr_fifo_tag_ff[i].addr <= obi_instr_addr;
          end else begin
            obi_instr_fifo_tag_ff[i]      <= obi_instr_fifo_tag_ff[i];
          end

          if (obi_data_fifo_tag_wena[i]) begin
            obi_data_fifo_tag_ff[i].tag  <= obi_data_request_n;
            obi_data_fifo_tag_ff[i].addr <= obi_data_addr;
          end else begin
            obi_data_fifo_tag_ff[i]      <= obi_data_fifo_tag_ff[i];
          end
        end
      end
    end

    always_comb begin
      case (obi_instr_fifo_tag_rena)
        8'b1 << 0: obi_instr_fifo_tag_out <= obi_instr_fifo_tag_ff[0];
        8'b1 << 1: obi_instr_fifo_tag_out <= obi_instr_fifo_tag_ff[1];
        8'b1 << 2: obi_instr_fifo_tag_out <= obi_instr_fifo_tag_ff[2];
        8'b1 << 3: obi_instr_fifo_tag_out <= obi_instr_fifo_tag_ff[3];
        8'b1 << 4: obi_instr_fifo_tag_out <= obi_instr_fifo_tag_ff[4];
        8'b1 << 5: obi_instr_fifo_tag_out <= obi_instr_fifo_tag_ff[5];
        8'b1 << 6: obi_instr_fifo_tag_out <= obi_instr_fifo_tag_ff[6];
        8'b1 << 7: obi_instr_fifo_tag_out <= obi_instr_fifo_tag_ff[7];
        default:   obi_instr_fifo_tag_out <= '0;
      endcase

      case (obi_data_fifo_tag_rena)
        8'b1 << 0: obi_data_fifo_tag_out <= obi_data_fifo_tag_ff[0];
        8'b1 << 1: obi_data_fifo_tag_out <= obi_data_fifo_tag_ff[1];
        8'b1 << 2: obi_data_fifo_tag_out <= obi_data_fifo_tag_ff[2];
        8'b1 << 3: obi_data_fifo_tag_out <= obi_data_fifo_tag_ff[3];
        8'b1 << 4: obi_data_fifo_tag_out <= obi_data_fifo_tag_ff[4];
        8'b1 << 5: obi_data_fifo_tag_out <= obi_data_fifo_tag_ff[5];
        8'b1 << 6: obi_data_fifo_tag_out <= obi_data_fifo_tag_ff[6];
        8'b1 << 7: obi_data_fifo_tag_out <= obi_data_fifo_tag_ff[7];
        default:   obi_data_fifo_tag_out <= '0;
      endcase
    end

    assign obi_instr_fifo_tag_we = obi_instr_push;
    assign obi_data_fifo_tag_we  = obi_data_push;

    assign obi_instr_fifo_tag_re = obi_instr_pop;
    assign obi_data_fifo_tag_re  = obi_data_pop ;

    property p_mtvt_table_read_equals_value_written;
      is_read_from_mtvt
      |->
        obi_instr_rdata == mtvt_table_value[(CLIC_ID_WIDTH)'((obi_instr_fifo_tag_out.addr - mtvt)/4)];

    endproperty : p_mtvt_table_read_equals_value_written

    property p_fencei_guarantee_visible_mtvt_write;
      accept_on(
        // Assume that mtvt is not changed - otherwise complexity of assertion explodes
        !$stable(mtvt, @(posedge clk_i))
      )
        s_store_mtvt_value
        ##1 (is_fencei_instr && rvfi_valid)[->1]
        ##1 (irq_ack && clic_core.shv)[->1]
        ##1 rvfi_valid[->1]
      |->
        // past because oic.id might have taken a new interrupt here, with cleared lower bit
        rvfi_pc_rdata == (($past(mtvt_table_value[clic_oic.id]) >> 1) << 1)
      or
        // Took debug instead, make sure dpc is correct
        rvfi_dbg
        && rvfi_pc_rdata == debug_halt_addr
        && (rvfi_dpc_rdata & rvfi_dpc_rmask) == (($past(mtvt_table_value[clic_oic.id]) >> 1) << 1)
      or
        is_invalid_instr_word
      or
        is_cause_nmi
      or
        is_trap_exception
      or
      // This should not be necessary, but inconsistent rvfi signaling on shv traps necessitates this check
        is_intr_exception
      ;
    endproperty : p_fencei_guarantee_visible_mtvt_write

    a_fencei_guarantee_visible_mtvt_write: assert property (p_fencei_guarantee_visible_mtvt_write)
    else
      `uvm_error(info_tag,
        $sformatf("Fencei should _always_ make writes to mtvt visible to next taken shv interrupt"));

    // ------------------------------------------------------------------------
    // mtvt aligned correctly
    // ------------------------------------------------------------------------

    property p_mtvt_alignment_correct;
      accept_on(N_MTVT <= 6) // Pass if field does not exist
      mtvt_fields.base_n_0 == '0;
    endproperty : p_mtvt_alignment_correct

    a_mtvt_alignment_correct: assert property (p_mtvt_alignment_correct)
    else
      `uvm_error(info_tag,
        $sformatf("mtvt alignment should have been %d bytes, mtvt: %08x",
          (2 ** N_MTVT),
          mtvt));

    // ------------------------------------------------------------------------
    // mepc is always set correctly when taking an interrupt
    // ------------------------------------------------------------------------

    logic [31:0] next_pc;

    // Formal tools generate warnings for latch behavior in assign statements, use explicit always_latch here
    always_latch begin
      next_pc <= !rst_ni ? '0 : rvfi_valid ? rvfi_pc_wdata : next_pc  ;
    end

    property p_mepc_set_correct_after_irq;
      logic [31:0] sampled_next_pc;
           // checks both csr_output and rvfi rdata
           irq_ack
       ##1 (1, sampled_next_pc    = rvfi_pc_wdata)
       ##0 rvfi_valid[->1]
      |->
           // 1. Normal case
           sampled_next_pc        == $past(next_pc) // should always match)
        && rvfi_intr.cause         < 'h400 // no nmi
        && rvfi_intr.exception    == 1'b0
        && rvfi_mepc_rdata        == $past(next_pc) // does not match with nmi
      or
           // 2. Nmi occurred
           sampled_next_pc        == $past(next_pc) // should always match
        && rvfi_intr.cause        >= 'h400
        && !(is_mepc_access_instr && is_csr_write)
        && rvfi_mepc_rdata        == (mtvec_fields & ~32'b11)
      or
           // 3. Handler rewrites mtvec addr, and nmi occurred on new mtvec
           sampled_next_pc        == $past(next_pc)
        && is_cause_nmi
        && is_mtvec_access_instr && is_csr_write
      or
           // 4. Handler rewrites mepc addr, and nmi occurred on new mepc
           sampled_next_pc        == $past(next_pc)
        && is_cause_nmi
        && is_mepc_access_instr && is_csr_write
      or
           // 5. Hardware vectored interrupt, but with instruction access fault exception on mtvt
           sampled_next_pc        == $past(next_pc)
        && clic_oic.shv           == 1'b1
        && rvfi_intr.cause        == 'h1
        && rvfi_mepc_rdata        == (mtvec_fields & ~32'b11)
      or
           // 6. Hardware vectored interrupt, but with instruction access fault on mtvt target
           sampled_next_pc        == $past(next_pc)
        && clic_oic.shv           == 1'b1
        && rvfi_intr.cause        == 'h1
        && rvfi_mepc_rdata        == mtvt_fields + (4 * clic_oic.id)
      or
           // 7. Hardware vectored interrupt without instruction access fault
           sampled_next_pc        == $past(next_pc)
        && clic_oic.shv           == 1'b1
        && rvfi_intr.exception    == 1'b0
        && rvfi_mepc_rdata        == sampled_next_pc
      or
           // 8. Last instruction prior to irq_ack enables irq, shv-irq and first instruction in handler gets interrupted
           // and this traps with instruction access fault
           // irq_ack followed by irq ack
           sampled_next_pc        == $past(next_pc)
        && $changed(clic_oic)     == 1'b1
        && $past(clic_oic.shv)    == 1'b1
        && rvfi_intr.cause        == 1'h1
        && rvfi_mepc_rdata        == mtvt_fields + (4 * $past(clic_oic.id))
      or
           // 9. Nested interrupt, with first being shv, second non-shv
           sampled_next_pc        == $past(next_pc)
        && $changed(clic_oic)     == 1'b1
        && $past(clic_oic.shv)    == 1'b1
        && clic_oic.shv           == 1'b0
        && rvfi_intr.cause        == 1'h1
        && rvfi_mepc_rdata        == mtvec_fields & ~32'b11
      or
           // 10. non-nested, mtvt fail with mtvt write
           sampled_next_pc        == $past(next_pc)
        && $stable(clic_oic)      == 1'b1
        && clic_oic.shv           == 1'b1
        && rvfi_intr.cause        == 1'h1
        && is_mtvt_access_instr && is_csr_write
        && rvfi_mepc_rdata        == $past(mtvt_fields) + (4 * clic_oic.id)
      or
           // 11. nested interrupts mtvt fail with mtvt write
           sampled_next_pc        == $past(next_pc)
        && $changed(clic_oic)     == 1'b1
        && $past(clic_oic.shv)    == 1'b1
        && rvfi_intr.cause        == 1'h1
        && is_mtvt_access_instr && is_csr_write
        && rvfi_mepc_rdata        == $past(mtvt_fields) + (4 * $past(clic_oic.id))
      ;
    endproperty : p_mepc_set_correct_after_irq;

    a_mepc_set_correct_after_irq: assert property (p_mepc_set_correct_after_irq)
    else
      `uvm_error(info_tag,
        $sformatf("Wrong mepc (0x%08x)",
          mepc_fields));

    // ------------------------------------------------------------------------
    // mcause.interrupt is always set when taking an interrupt
    // ------------------------------------------------------------------------

    property p_mcause_interrupt_always_set_on_taken_irq;
          irq_ack
      |=>
          mcause_fields.interrupt;
    endproperty : p_mcause_interrupt_always_set_on_taken_irq

    a_mcause_interrupt_always_set_on_taken_irq: assert property (p_mcause_interrupt_always_set_on_taken_irq)
    else
      `uvm_error(info_tag,
        $sformatf("mcause.interrupt should be set on taken interrupts"));

    // ------------------------------------------------------------------------
    // mcause.cause is always set correctly after taking an interrupt
    // ------------------------------------------------------------------------

    property p_mcause_exccode_always_set_correctly_on_taken_irq;
          irq_ack
      |=>
          mcause_fields.n.exccode_10_0 == $past(clic_core.id);
    endproperty : p_mcause_exccode_always_set_correctly_on_taken_irq

    a_mcause_exccode_always_set_correctly_on_taken_irq: assert property (p_mcause_exccode_always_set_correctly_on_taken_irq)
    else
      `uvm_error(info_tag,
        $sformatf("mcause.exccode should be set on taken interrupts"));


    // ------------------------------------------------------------------------
    // mcause.mpil should reflect the previous privilege mode after taking
    // an interrupt
    // ------------------------------------------------------------------------

    property p_mcause_mpil_reflects_previous_interrupt_lvl;
      bit [7:0] il_prev;
      (irq_ack, il_prev = mintstatus_fields.mil) |=> mcause_fields.mpil == il_prev;
    endproperty : p_mcause_mpil_reflects_previous_interrupt_lvl

    a_mcause_mpil_reflects_previous_interrupt_lvl: assert property (p_mcause_mpil_reflects_previous_interrupt_lvl)
    else
      `uvm_error(info_tag,
        $sformatf("mpil wrong, value: %0d",
          mcause_fields.mpil));

    // ------------------------------------------------------------------------
    // mcause.mpp should reflect the previous privilege mode after taking an
    // interrupt
    // ------------------------------------------------------------------------

    property p_mcause_we_cover;
      reject_on(rvfi_trap)
           is_mcause_access_instr
        && csr_instr.n.rs1 != 0
        && csr_instr.rd != 0
        && (~|rvfi_trap)
        && rvfi_valid
        ##1
           rvfi_valid[=5];
    endproperty : p_mcause_we_cover

    property p_mstatus_we_cover;
      reject_on(rvfi_trap)
            is_mstatus_access_instr
         && csr_instr.n.rs1 != 0
         && csr_instr.rd != 0
         && (~|rvfi_trap)
         && rvfi_valid
        ##1
           rvfi_valid[=5];
    endproperty : p_mstatus_we_cover

    property p_mnxti_we_cover;
      reject_on(rvfi_trap)
            is_mnxti_access_instr
         && csr_instr.n.rs1 != 0
         && csr_instr.rd != 0
         && (~|rvfi_trap)
         && rvfi_valid
        ##1
            rvfi_valid[=5];
    endproperty : p_mnxti_we_cover

    property p_mstatus_mpp_neq_mcause_mpp;
      mstatus_fields.mpp == mcause_fields.mpp;
    endproperty : p_mstatus_mpp_neq_mcause_mpp

    property p_mstatus_mpie_neq_mcause_mpie;
      mstatus_fields.mpie == mcause_fields.mpie;
    endproperty : p_mstatus_mpie_neq_mcause_mpie

    a_mpp: assert property (p_mstatus_mpp_neq_mcause_mpp)
    else
      `uvm_error(info_tag, "'mstatus.mpp' must match 'mcause.mpp'");
    a_mpie: assert property (p_mstatus_mpie_neq_mcause_mpie)
    else
      `uvm_error(info_tag, "'mstatus.mpie' must match 'mcause.mpie'");

    property p_mcause_mpp_reflects_previous_privilege_mode;
      bit [1:0] mode_prev = 2'b11;
      irq_ack
      |=>
      mcause_fields.mpp == $past(current_priv_mode);
    endproperty : p_mcause_mpp_reflects_previous_privilege_mode

    a_mcause_mpp_reflects_previous_privilege_mode: assert property (p_mcause_mpp_reflects_previous_privilege_mode)
    else
      `uvm_error(info_tag,
        $sformatf("Previous privilege wrong, mpp value: %02b",
          mcause_fields.mpp));

    // ------------------------------------------------------------------------
    // mcause.mpie should reflect the previous interrupt enable after taking
    // an interrupt
    // ------------------------------------------------------------------------

    property p_mcause_mpie_reflects_previous_interrupt_enable;
      bit mpie_prev;
      (irq_ack, mpie_prev = mstatus_fields.mie) |=> mstatus_fields.mpie == mpie_prev;
    endproperty  : p_mcause_mpie_reflects_previous_interrupt_enable

    a_mcause_mpie_reflects_previous_interrupt_enable: assert property (p_mcause_mpie_reflects_previous_interrupt_enable)
    else
      `uvm_error(info_tag,
        $sformatf("mpie wrong, value: %0b",
          mcause_fields.mpie));

    // ------------------------------------------------------------------------
    // mnxti should return the value of the currently taken interrupt
    // if the pending interrupt in clic is the same as the interrupt id
    // in the current context
    // ------------------------------------------------------------------------

    always_latch begin
      clic_oic <= !rst_ni ? '0 : irq_ack ? clic_core : clic_oic;
    end

    sequence seq_irq_req_unchanged;
      @(posedge clk_i)

      clic == clic_oic;
    endsequence : seq_irq_req_unchanged

    sequence seq_valid_irq_pending(s_clic);
      clic_irq_bundle_t sampled_clic = s_clic;

      @(posedge clk_i)

         sampled_clic.priv == M_MODE
      && sampled_clic.level > mcause_fields.mpil
      && sampled_clic.level > mintthresh_fields.th
      && !sampled_clic.shv
      && csr_instr.rd;
    endsequence : seq_valid_irq_pending

    property p_mnxti_case_1_irq_req_unchanged;
      // Due to simulator issues (xcelium) one cannot sample sampled_clic = clic, must sample individual signals
      clic_irq_bundle_t sampled_clic;
          (seq_irq_req_unchanged.triggered,
            sampled_clic.irq   = clic.irq,
            sampled_clic.id    = clic.id,
            sampled_clic.level = clic.level,
            sampled_clic.priv  = clic.priv,
            sampled_clic.shv   = clic.shv)
        ##2
            is_valid_mnxti_read && !irq_ack
      |->
            // Return pointer to current interrupt entry
                (rvfi_rd_wdata == mtvt_fields + (clic_oic.id * 4))
             && sampled_clic.irq
             && sampled_clic.priv == M_MODE
             && sampled_clic.level > mcause_fields.mpil
             && sampled_clic.level > mintthresh_fields.th
             && !sampled_clic.shv
             && csr_instr.rd
      or
             // Return 0 if no irq, not higher level, or shv, or previous mnxti updated the context such that the previous
             // levels are no longer valid or destination register = x0
                rvfi_rd_wdata == 0
             && !(sampled_clic.irq
               && sampled_clic.priv == M_MODE
               && sampled_clic.level > mcause_fields.mpil
               && sampled_clic.level > mintthresh_fields.th
               && !sampled_clic.shv)
      or
            // Destination register is x0 (zero) - no read value
                rvfi_rd_wdata == 0
            &&  csr_instr.rd == X0
      or
                rvfi_trap.debug
      or
                rvfi_trap.exception
      ;
    endproperty : p_mnxti_case_1_irq_req_unchanged

    a_mnxti_case_1_irq_req_unchanged: assert property (p_mnxti_case_1_irq_req_unchanged)
    else
      `uvm_error(info_tag,
        $sformatf("No change on pending interrupt, mnxti incorrect result"));

    // ------------------------------------------------------------------------
    // mnxti should return the table entry for the new, higher level
    // interrupt when this new interrupt has superceeded the initial
    // interrupt.
    // ------------------------------------------------------------------------

    sequence seq_higher_lvl_nonshv_clic_taken;
      @(posedge clk_i)

          clic.irq
       && clic.level > mcause_fields.mpil
       && clic.level > mintthresh_fields.th
       && clic.priv == clic_oic.priv
       && !clic.shv;
    endsequence : seq_higher_lvl_nonshv_clic_taken

    property p_mnxti_case_2_replaced_by_higher_level_non_shv_irq;
      logic [CLIC_ID_WIDTH-1:0] sampled_clic_id;
            (seq_higher_lvl_nonshv_clic_taken.triggered, sampled_clic_id = clic.id)
        ##2
            is_valid_mnxti_read
      |->
            // Return pointer to current interrupt entry
            (rvfi_rd_wdata == mtvt_fields + (sampled_clic_id * 4))
      or
            // rvfi masks out reads that are written to x0
            csr_instr.rd == X0
         && rvfi_rd_wdata == 0
      or
            rvfi_trap.debug
      or
            rvfi_trap.exception;
    endproperty : p_mnxti_case_2_replaced_by_higher_level_non_shv_irq


    a_mnxti_case_2_replaced_by_higher_level_non_shv_irq: assert property (p_mnxti_case_2_replaced_by_higher_level_non_shv_irq)
    else
      `uvm_error(info_tag,
        $sformatf("interrupt replaced by higher level non-shv interrupt, mnxti incorrect result"));

    // ------------------------------------------------------------------------
    // mnxti should return the value of the lower leveled interrupt
    // when the original interrupt is no longer present and the new
    // interrupt has a level higher than the interrupted context
    // already in clic
    // ------------------------------------------------------------------------

    sequence seq_lower_oic_no_longer_presesnt_lower_lvl_pending;
      @(posedge clk_i)

          clic.irq
       && clic.level > mcause_fields.mpil
       && clic.level <= clic_oic.level
       && clic.level > mintthresh_fields.th
       && clic.priv == clic_oic.priv
       && !clic.shv;
    endsequence : seq_lower_oic_no_longer_presesnt_lower_lvl_pending

    property p_mnxti_case_4_replaced_by_lower_level_irq;
      logic [CLIC_ID_WIDTH-1:0] sampled_clic_id;
        seq_higher_lvl_nonshv_clic_taken.triggered
        ##2 is_valid_mnxti_write
        ##1 (seq_lower_oic_no_longer_presesnt_lower_lvl_pending.triggered[->1], sampled_clic_id = clic.id)
        ##2 is_valid_mnxti_read
      |->
        (rvfi_rd_wdata == mtvt_fields + (sampled_clic_id * 4))
      or
        csr_instr.rd  == X0
        && rvfi_rd_wdata == 0
      or
        rvfi_trap.debug
      or
        rvfi_trap.exception;
    endproperty : p_mnxti_case_4_replaced_by_lower_level_irq

    a_mnxti_case_4_replaced_by_lower_level_irq: assert property (p_mnxti_case_4_replaced_by_lower_level_irq)
    else
      `uvm_error(info_tag,
        $sformatf("interrupt replaced by lower level interrupt, mnxti result incorrect"));

    // ------------------------------------------------------------------------
    // mnxti should read zero if the original interrupt is no longer asserted
    // ------------------------------------------------------------------------

    property p_mnxti_case_5_1_no_current_irq;
          !clic.irq
      ##2 is_valid_mnxti_read
      |->
          rvfi_rd_wdata == 32'h0000_0000;
    endproperty : p_mnxti_case_5_1_no_current_irq

    a_mnxti_case_5_1_no_current_irq : assert property (p_mnxti_case_5_1_no_current_irq)
    else
      `uvm_error(info_tag,
        $sformatf("mnxti should read zero when no irq is present"));

    // ------------------------------------------------------------------------
    // mnxti should read zero if the current pending interrupt has a
    // level lower than mpil
    // ------------------------------------------------------------------------

    sequence seq_nonshv_lower_lvl_pending;
      @(posedge clk_i)

           clic.irq
       && !clic.shv
       && (clic.level < mcause_fields.mpil);
    endsequence : seq_nonshv_lower_lvl_pending

    property p_mnxti_case_5_2_lvl_nonshv_pending;
          seq_nonshv_lower_lvl_pending.triggered
      ##2 is_valid_mnxti_read
      |->
          rvfi_rd_wdata == 32'h0000_0000;
    endproperty : p_mnxti_case_5_2_lvl_nonshv_pending

    a_mnxti_case_5_2_lvl_nonshv_pending : assert property (p_mnxti_case_5_2_lvl_nonshv_pending)
    else
      `uvm_error(info_tag,
        $sformatf("mnxti should read zero when irq is lower level and non-shv"));

    // ------------------------------------------------------------------------
    // mnxti should read zero if higher level shv interrupt has succeeded
    // the initial interrerupt
    // ------------------------------------------------------------------------

    sequence seq_higher_lvl_shv_irq_pending;
      @(posedge clk_i)

          clic.irq
       && clic.shv
       && clic.level > mintthresh_fields.th
       && clic.level > mcause_fields.mpil;
    endsequence : seq_higher_lvl_shv_irq_pending

    property p_mnxti_case_6_higher_level_irq_superceed;
          seq_higher_lvl_shv_irq_pending.triggered
      ##2 is_valid_mnxti_read
      |->
          rvfi_rd_wdata == 32'h0000_0000;
    endproperty : p_mnxti_case_6_higher_level_irq_superceed

    a_mnxti_case_6_higher_level_irq_superceed: assert property (p_mnxti_case_6_higher_level_irq_superceed)
    else
      `uvm_error(info_tag,
        $sformatf("mnxti should read zero when a higher level shv interrupt is pending"));

    // ------------------------------------------------------------------------
    // mnxti CSR side effects on write
    // ------------------------------------------------------------------------

    sequence seq_pending_nonshv_irq;
      @(posedge clk_i)

          clic.irq
       && !clic.shv
       && clic.level > mintthresh_fields.th
       && clic.level > mcause_fields.mpil
       && clic.priv == M_MODE;
    endsequence : seq_pending_nonshv_irq

    property p_mnxti_side_effects_on_write;
      logic [$bits(clic.id)-1:0] sampled_id;
      logic [$bits(clic.level)-1:0] sampled_level;

          (seq_pending_nonshv_irq,
            // Sampled values
            sampled_id = clic.id,
            sampled_level = clic.level)
      ##2 is_valid_mnxti_write
       && !rvfi_trap.exception
       && !rvfi_trap.debug
      |->
            (mintstatus_fields.mil        == sampled_level)
         && (mcause_fields.n.exccode_10_0 == sampled_id)
         && (mcause_fields.interrupt      == 1'b1)

         // TODO: The code below should work, but fails with xcelium - evaluate if this can
         // be reenabled if this issue is fixed (needs changes to sampling code above as well):

         //   (mintstatus_fields.mil == sampled_clic.level)
         //&& (mcause_fields.n.exccode_10_0 == sampled_clic.id)
         //&& (mcause_fields.interrupt == 1'b1)
      ;

    endproperty : p_mnxti_side_effects_on_write

    a_mnxti_side_effects_on_write: assert property (p_mnxti_side_effects_on_write)
    else
      `uvm_error(info_tag,
        $sformatf("Side effects on mnxti write wrong"));

    property p_mnxti_no_side_effects_on_no_write;
           !is_valid_mnxti_write
        && is_mnxti_access_instr
      |->
           // no change unless trap (below)
           $stable(mintstatus_fields)
        && $stable(mcause_fields)
      or
           // mintstatus static if horizontal trap,
           // mcause allowed to change
           $stable(mintstatus_fields)
        && rvfi_trap.exception
        && rvfi_trap.trap
       ##1
           rvfi_valid[->1]
       ##0
           rvfi_intr.exception
        && rvfi_intr.intr
        && $stable(rvfi_mode)
      or
           // Clear mintstatus.mil for vertical traps
           // mcause allowed to change
            mintstatus_fields.mil == 'h0
         && rvfi_trap.exception
         && rvfi_trap.trap
        ##1
            rvfi_valid[->1]
        ##0
            rvfi_intr.exception
         && rvfi_intr.intr
         && $changed(rvfi_mode)
      or
        // NMI
            //$stable(mintstatus_fields) // FIXME reintroduce to not overconstrain
        ##1 rvfi_valid[->1]
        ##0 rvfi_intr.interrupt
        &&  rvfi_intr.cause >= 'h400
      ;
    endproperty :  p_mnxti_no_side_effects_on_no_write

    a_mnxti_no_side_effects_on_no_write: assert property (p_mnxti_no_side_effects_on_no_write)
    else
      `uvm_error(info_tag,
        $sformatf("Should be no side effects on no mnxti write"));

    // ------------------------------------------------------------------------
    // Mintstatus should be updated on ISR handler entry
    // ------------------------------------------------------------------------

    property p_mintstatus_updated_on_isr_handler_entry;
            clic.irq
        ##1 irq_ack
        |=>
            mintstatus_fields.mil == clic_oic.level &&
            mintstatus_fields.sil == 8'h00 &&
            mintstatus_fields.uil == 8'h00;
    endproperty : p_mintstatus_updated_on_isr_handler_entry

    a_mintstatus_updated_on_isr_handler_entry: assert property(p_mintstatus_updated_on_isr_handler_entry)
    else
      `uvm_error(info_tag,
        $sformatf("Minstatus mismatch, read 0x%08h",
          mintstatus_fields));

    // ------------------------------------------------------------------------
    // Minhv should be set when an shv interrupt is taken
    // ------------------------------------------------------------------------

    property p_mcause_minhv_set_at_hw_vectoring_start;
          clic.shv
      ##1 irq_ack
        |=>
          mcause_fields.minhv;
    endproperty : p_mcause_minhv_set_at_hw_vectoring_start

    a_mcause_minhv_set_at_hw_vectoring_start: assert property (p_mcause_minhv_set_at_hw_vectoring_start)
    else
      `uvm_error(info_tag,
        $sformatf("mcause.minhv not set at hw vectored ISR entry"));

    // ------------------------------------------------------------------------
    // Minhv should be cleared on successful pointer fetch
    // ------------------------------------------------------------------------

    property p_mcause_minhv_cleared_at_hw_vectoring_end;
      $rose(mcause_fields.minhv)
      && !(csr_instr.csr == MCAUSE)
      ##1 rvfi_valid[->1]
        |->
          mcause_fields.minhv == 1'b0
      or
          // minhv set by write to mcause
          is_mcause_access_instr
       && is_csr_write
       && rvfi_rs1_rdata[30] == 1'b1
       && mcause_fields.minhv == 1'b1
      or
          is_instr_clicptr_fault
       && mcause_fields.minhv == 1'b1
      or
          // vectored address failed
          is_invalid_instr_word
       && mcause_fields.minhv == 1'b1
      or
          // Access fault to destination
          (is_cause_instr_access_fault || is_cause_instr_bus_fault || is_cause_instr_parity_fault)
       && mcause_fields.minhv == 1'b1
      ;
    endproperty : p_mcause_minhv_cleared_at_hw_vectoring_end

    a_mcause_minhv_cleared_at_hw_vectoring_end: assert property (p_mcause_minhv_cleared_at_hw_vectoring_end)
    else
      `uvm_error(info_tag,
        $sformatf("mcause.minhv not cleared at hw vectored fetch")
      );

    // ------------------------------------------------------------------------
    // Cover: minhv cleared at hw vectoring end (successful pointer fetch)
    // ------------------------------------------------------------------------

    property cp_mcause_minhv_cleared_at_hw_vectoring_end;
      strong(
          $rose(mcause_fields.minhv)
          && !(csr_instr.csr == MCAUSE)
          ##1 $fell(mcause_fields.minhv)[->1]
        and
          1 ##1 rvfi_valid[->1]
      );
    endproperty : cp_mcause_minhv_cleared_at_hw_vectoring_end

    cov_mcause_minhv_cleared_at_hw_vectoring_end: cover property(cp_mcause_minhv_cleared_at_hw_vectoring_end);

    // ------------------------------------------------------------------------
    // No prefetches between pointer fetch and final target
    // ------------------------------------------------------------------------

    property p_no_prefetches_between_ptr_fetch_and_final_target;
      clic.shv
      ##1 irq_ack
      ##1 mcause_fields.minhv
      && !(csr_instr.csr == MCAUSE)
        |=>
      (obi_instr_req && obi_instr_gnt)[->1]
      ##0 $fell(mcause_fields.minhv)[->1];
    endproperty : p_no_prefetches_between_ptr_fetch_and_final_target

    a_no_prefetches_between_ptr_fetch_and_final_target: assert property (p_no_prefetches_between_ptr_fetch_and_final_target)
    else
      `uvm_error(info_tag,
        $sformatf("There should be no prefeches between ptr fetch and final target"));

    // ------------------------------------------------------------------------
    // Cover: No prefetches between pointer fetch and final target
    // ------------------------------------------------------------------------

    property cp_no_prefetches_between_ptr_fetch_and_final_target;
      reject_on(core_in_debug)
      clic.shv
      ##1 irq_ack
      ##1 mcause_fields.minhv
        && !(csr_instr.csr == MCAUSE)
      #=#
      (obi_instr_req && obi_instr_gnt)[->1]
      ##0 $fell(mcause_fields.minhv)[->1];
    endproperty : cp_no_prefetches_between_ptr_fetch_and_final_target

    cov_no_prefetches_between_ptr_fetch_and_final_target: cover property (cp_no_prefetches_between_ptr_fetch_and_final_target);

    // ------------------------------------------------------------------------
    // PC should be set to the address fetched from the mtvt pointer after
    // taking an shv interrupt
    // ------------------------------------------------------------------------

    sequence s_shv_irq_no_pending_obi;
      1 ##1 !obi_instr_pending
        && clic.irq
        && clic.shv
      ##1 irq_ack
      ;
    endsequence : s_shv_irq_no_pending_obi

    sequence s_shv_irq_pending_obi;
      1 ##1 obi_instr_pending
        && clic.irq
        && clic.shv
      ##1 irq_ack
      ;
    endsequence : s_shv_irq_pending_obi

    property p_pc_to_mtvt_for_taken_shv_interrupt_outstanding_obi;
      logic [31:0] pointer_value = '0;
      logic [31:0] pointer_addr = '0;
      logic [3:0] pointer_req = '0;

      s_shv_irq_pending_obi
      // Need to finish outstanding obi txn first then get the correct address
      ##0 (obi_instr_push[->2],
           // Sample address for pointer fetch
           pointer_addr = obi_instr_addr,
           pointer_req  = obi_instr_request_n)
           // Wait for rdata and sample expected pc
      ##1 ((pointer_req == obi_instr_service_n)[->1])
      ##0 (1, pointer_value = obi_instr_rdata)
      ##0 mcause_fields.minhv
      ##0 rvfi_valid[->1]
      |->
        rvfi_pc_rdata                   == (pointer_value & ~1)
       // use past here as these may be updated by handler instruction or new interrupt
       && $past(mtvt_fields) + ($past(clic_oic.id) * 4) == (pointer_addr)
       // minhv should be cleared unless explicitly written to
       && ((!mcause_fields.minhv && !(is_mcause_access_instr && is_csr_write && rvfi_mcause_wmask[30] && rvfi_mcause_wdata[30]))
          || (mcause_fields.minhv && (is_mcause_access_instr && is_csr_write && rvfi_mcause_wmask[30] && rvfi_mcause_wdata[30])))
      or
        is_cause_nmi // nmi-address verified in nmi-related assertions
      or
        is_invalid_instr_word
       && rvfi_pc_rdata       == { $past(mtvec[31:7]), 7'h0 }
      or
        is_cause_instr_access_fault || is_cause_instr_bus_fault || is_cause_instr_parity_fault
      or
        is_instr_access_fault
      or
        is_instr_clicptr_fault
      or
        is_mstatus_access_instr && is_csr_write && mstatus_fields.mie
       && irq_ack
      or
        is_mnxti_access_instr && is_csr_write && mstatus_fields.mie
       && irq_ack
      or
        is_mret_instr && $past(mstatus_fields.mpie)
       && irq_ack
      or
      rvfi_dbg_mode
      ;
    endproperty : p_pc_to_mtvt_for_taken_shv_interrupt_outstanding_obi

    a_pc_to_mtvt_for_taken_shv_interrupt_outstanding_obi: assert property (p_pc_to_mtvt_for_taken_shv_interrupt_outstanding_obi)
    else
      `uvm_error(info_tag,
        $sformatf("Pc should be at mtvt after taking an shv interrupt"));

    property p_pc_to_mtvt_for_taken_shv_interrupt;
      logic [31:0] pointer_value = '0;
      logic [31:0] pointer_addr = '0;
      logic [3:0] pointer_req = '0;
      s_shv_irq_no_pending_obi
      ##0 (obi_instr_push[->1],
           // Sample address for pointer fetch
           pointer_addr = obi_instr_addr,
           pointer_req  = obi_instr_request_n)
           // Wait for rdata and sample expected pc
      ##1 ((pointer_req == obi_instr_service_n)[->1])
      ##0 (1, pointer_value = obi_instr_rdata)
      ##0 mcause_fields.minhv
      ##0 rvfi_valid[->1]
      |->
        // Normal case, should end up at mtvt
        rvfi_pc_rdata                   == (pointer_value & ~1)
       && $past(mtvt_fields) + ($past(clic_oic.id) * 4) == (pointer_addr)
       // minhv should be cleared unless explicitly written to
       && ((!mcause_fields.minhv && !(is_mcause_access_instr && is_csr_write && rvfi_mcause_wmask[30] && rvfi_mcause_wdata[30]))
          || (mcause_fields.minhv && (is_mcause_access_instr && is_csr_write && rvfi_mcause_wmask[30] && rvfi_mcause_wdata[30])))
      or
        is_cause_nmi // nmi-address verified in nmi-related assertions
      or
        is_invalid_instr_word
       && rvfi_pc_rdata       == { $past(mtvec[31:7]), 7'h0 }
      or
        is_cause_instr_access_fault || is_cause_instr_bus_fault || is_cause_instr_parity_fault
      or
        is_instr_access_fault
      or
        is_instr_clicptr_fault
      or
        is_mstatus_access_instr && is_csr_write && mstatus_fields.mie
       && irq_ack
      or
        is_mnxti_access_instr && is_csr_write && mstatus_fields.mie
       && irq_ack
      or
        is_mret_instr && $past(mstatus_fields.mpie)
       && irq_ack
      or
        rvfi_dbg_mode
      ;

    endproperty : p_pc_to_mtvt_for_taken_shv_interrupt

    a_pc_to_mtvt_for_taken_shv_interrupt: assert property (p_pc_to_mtvt_for_taken_shv_interrupt)
    else
      `uvm_error(info_tag,
        $sformatf("Pc should be at mtvt after taking an shv interrupt"));

    // ------------------------------------------------------------------------
    // PC should be set to mtvec for taken non-shv interrupt
    // ------------------------------------------------------------------------

    property p_pc_to_mtvec_for_taken_nonshv_interrupt;
            clic.irq
        &&  !clic.shv
        ##1 irq_ack
        ##1 rvfi_valid[->1]
      |->
          // Need to use past here to avoid the case where mtvec is updated simultaneously
          rvfi_pc_rdata[31:7] == $past(mtvec[31:7])
      or
          // Nmi, correct pc covered in a_nmi_to_mtvec_offset
          is_cause_nmi
      or
          is_instr_access_fault
      or
         rvfi_dbg_mode
      ;
    endproperty : p_pc_to_mtvec_for_taken_nonshv_interrupt

    a_pc_to_mtvec_for_taken_nonshv_interrupt: assert property (p_pc_to_mtvec_for_taken_nonshv_interrupt)
    else
      `uvm_error(info_tag,
        $sformatf("Pc should be at mtvec after taking a non-shv interrupt"));

    // ------------------------------------------------------------------------
    // Correct alignment of the taken non-shv interrupt address
    // ------------------------------------------------------------------------

    property p_pc_alignment_of_taken_non_shv_interrupt;
            irq_ack
        &&  !clic_core.shv
        ##1 rvfi_valid[->1]
      |->
            // Exceptions/interrupts should jump to base address,
            // and base addr. should be aligned
            !is_cause_nmi
         && rvfi_pc_rdata[6:0] == 7'b000_0000
      or
            is_cause_nmi
         && rvfi_pc_rdata[6:0] == NMI_OFFSET // == all zeros + NMI_OFFSET in table
      or
            rvfi_dbg_mode
      ;
    endproperty : p_pc_alignment_of_taken_non_shv_interrupt

    a_pc_alignment_of_taken_non_shv_interrupt: assert property (p_pc_alignment_of_taken_non_shv_interrupt)
    else
      `uvm_error(info_tag,
        $sformatf("Non-shv interrupt taken should have a PC aligned with bits 6:0 = 0"));

    // ------------------------------------------------------------------------
    // Interrupt taken if, and only if the following matches:
    // ------------------------------------------------------------------------
    // ------------------------------------------------------------------------
    // Higher level than mintthresh.th interrupts can preempt
    // ------------------------------------------------------------------------
    property p_higher_lvl_than_mintthresh_th_can_preempt;
            clic.irq
        ##1 ($past(clic.priv) == current_priv_mode)
        &&  ($past(clic.level) > effective_clic_level)
        &&  mstatus_fields.mie
        &&  is_interrupt_allowed == 1'b1
      |->
            irq_ack
      or
            rvfi_valid[->1:2]
        ##0 rvfi_dbg_mode
      or
            rvfi_valid[->1:2]
        ##0 rvfi_intr.exception
      or
            rvfi_valid[->1:2]
        ##0 rvfi_trap.exception
      or
            rvfi_valid[->1:2]
        ##0 is_cause_nmi
      ;
    endproperty : p_higher_lvl_than_mintthresh_th_can_preempt

    a_higher_lvl_than_mintthresh_th_can_preempt: assert property(p_higher_lvl_than_mintthresh_th_can_preempt)
    else
      `uvm_error(info_tag,
        $sformatf("Higher level than mintthresh should be able to interrupt"));

    // ------------------------------------------------------------------------
    // Lower level than mintthresh.th interrupts cannot preempt
    // ------------------------------------------------------------------------
    property p_lower_lvl_than_mintthresh_th_cannot_preempt;
          clic.irq
      ##1 $past(clic.level) < mintthresh_fields.th
      &&  $past(clic.priv) == current_priv_mode
      |->
          !irq_ack;
    endproperty : p_lower_lvl_than_mintthresh_th_cannot_preempt

    a_lower_lvl_than_mintthresh_th_cannot_preempt: assert property (p_lower_lvl_than_mintthresh_th_cannot_preempt)
    else
      `uvm_error(info_tag,
        $sformatf("Lower than mintthresh.th level interrupts should not preempt"));

    // ------------------------------------------------------------------------
    // WFI wakeup required
    // ------------------------------------------------------------------------
    property p_wfi_wfe_wakeup_condition_valid;
      logic             sampled_wfe_wakeup_event;
      clic_irq_bundle_t sampled_clic;
      logic [7:0]       sampled_level;
      priv_mode_t       sampled_priv;

      core_sleep_o ##1 // first cycle $fell will fail out of reset
            ($fell(core_sleep_o),
              sampled_clic.irq   = clic.irq,
              sampled_clic.id    = clic.id,
              sampled_clic.level = clic.level,
              sampled_clic.priv  = clic.priv,
              sampled_clic.shv   = clic.shv,
              sampled_priv = priv_mode_t'(current_priv_mode),
              sampled_level = effective_clic_level,
              sampled_wfe_wakeup_event = is_wfe_wakeup_event)
        ##1 rvfi_valid[->1]
      |->
        // Interrupt triggered wake up  *both wfe and wfi*
        ##0 sampled_clic.irq
         && sampled_clic.priv  == sampled_priv
         && sampled_clic.level > sampled_level
      or
        // Interrupt triggered wake up  *both wfe and wfi*
        ##0 sampled_clic.irq
         && sampled_clic.priv  > sampled_priv
         && sampled_clic.level > 0
      or
        // Debug request *both wfe and wfi*
        ##1 rvfi_valid[->1]
        ##0 rvfi_dbg_mode == 1'b1
      or
        // Wakeup from wfe-pin, *wfe only*
            is_wfe_instr
        ##0 sampled_wfe_wakeup_event
      ;
    endproperty : p_wfi_wfe_wakeup_condition_valid

    a_wfi_wfe_wakeup_condition_valid: assert property (p_wfi_wfe_wakeup_condition_valid)
    else
      `uvm_error(info_tag,
        $sformatf("core should have woken up"));

    // ------------------------------------------------------------------------
    // WFI wakeup forbidden
    // ------------------------------------------------------------------------
    property p_wfi_wfe_wakeup_condition_not_valid;
        core_sleep_o
      ##1
       !((  clic.irq
         && clic.priv  == priv_mode_t'(current_priv_mode)
         && clic.level > effective_clic_level)
       ||
        (   clic.irq
         && clic.priv  > priv_mode_t'(current_priv_mode)
         && clic.level > 0))
      |->
        // Stay asleep
        $stable(core_sleep_o)
      or
        // We slept due to wfe, pin can wake us up
            is_wfe_wakeup_event
        ##0 !core_sleep_o
        ##0 rvfi_valid[->1]
        ##0 is_wfe_instr

      or
        // We woke up due to a debug request, first retire wfi, then take debug
            !core_sleep_o
        ##0 rvfi_valid[->2]
        ##0 rvfi_dbg_mode
      ;
    endproperty : p_wfi_wfe_wakeup_condition_not_valid

    a_wfi_wfe_wakeup_condition_not_valid: assert property (p_wfi_wfe_wakeup_condition_not_valid)
    else
      `uvm_error(info_tag,
        $sformatf("core should not have woken up"));

    // ------------------------------------------------------------------------
    // WFI entry causes core to stop
    // ------------------------------------------------------------------------
    property p_wfi_wfe_causes_core_to_stop;
      core_sleep_o
      |->
        !rvfi_valid
      ;
    endproperty : p_wfi_wfe_causes_core_to_stop

    a_wfi_wfe_causes_core_to_stop: assert property (p_wfi_wfe_causes_core_to_stop)
    else
      `uvm_error(info_tag,
        $sformatf("core should not execute anything in wfi"));

    // ------------------------------------------------------------------------
    // WFI entry causes core clock to be gated
    // ------------------------------------------------------------------------
    property p_wfi_wfe_causes_clock_gating;
      core_sleep_o
      |->
        $stable(clk)
      ;
    endproperty : p_wfi_wfe_causes_clock_gating

    a_wfi_wfe_causes_clock_gating: assert property (p_wfi_wfe_causes_clock_gating)
    else
      `uvm_error(info_tag,
        $sformatf("core clk should be gated in wfi"));

    // ------------------------------------------------------------------------
    // WFI: core_sleep_o only asserted during wfi
    // ------------------------------------------------------------------------
    property p_core_sleep_o_only_during_wfi_wfe;
        core_sleep_o
        ##0 rvfi_valid[->1]
      |->
        is_wfi_instr
      or
        is_wfe_instr
      ;
    endproperty : p_core_sleep_o_only_during_wfi_wfe

    a_core_sleep_o_only_during_wfi_wfe: assert property (p_core_sleep_o_only_during_wfi_wfe)
    else
      `uvm_error(info_tag,
        $sformatf("core_sleep_o should only be asserted during wfi"));

    // ------------------------------------------------------------------------
    // Correct state of core after mret
    // Regular execution (excludes debug, exceptions etc...)
    // ------------------------------------------------------------------------

    logic irq_ack_occurred_between_valid;
    logic minhv_high_between_valid;

    always @(posedge clk_i) begin
      if (!rst_ni || (rvfi_valid && !irq_ack)) begin
        irq_ack_occurred_between_valid <= 1'b0;
      end else begin
        irq_ack_occurred_between_valid <= irq_ack_occurred_between_valid ? 1'b1 : irq_ack;
      end
    end

    always @(posedge clk_i) begin
      if (!rst_ni || rvfi_valid && !mcause_fields.minhv) begin
        minhv_high_between_valid <= 1'b0;
      end else begin
        minhv_high_between_valid <= minhv_high_between_valid ? 1'b1 : mcause_fields.minhv;
      end
    end

    property p_irq_ack_occurred_zero_out_of_reset;
        !fetch_enable |-> irq_ack_occurred_between_valid == 1'b0;
    endproperty : p_irq_ack_occurred_zero_out_of_reset

    //// WIP section start ////
    //TODO:MT The following code is a work in progress, but is checked in to indicate that
    //        the exisiting asserts are not expected to be relied upon


    // mret should continue at mepc
    // this checks the intention at retirement of mepc, not that the next instruction is correct.
    property p_mret_pc_not_vectored_intended;
      rvfi_if.is_mret
      && !rvfi_if.rvfi_trap.trap
      && !rvfi_mcause_fields.minhv
      |->
        rvfi_if.rvfi_pc_wdata == csr_mepc_if.rvfi_csr_rdata;
    endproperty : p_mret_pc_not_vectored_intended

    a_mret_pc_not_vectored_intended: assert property (p_mret_pc_not_vectored_intended)
    else
      `uvm_error(info_tag,
        $sformatf("mret result state incorrect"));


    // this checks the intention at retirement of mepc, not that the next instruction is correct.
    property p_mret_pc_not_vectored_1;
      rvfi_if.is_mret
      && !rvfi_if.rvfi_trap.trap
      && !rvfi_mcause_fields.minhv

      ##1 rvfi_valid[->1]
      ##0 !(rvfi_if.rvfi_intr.intr || support_if.first_debug_ins)
      |->
        rvfi_if.rvfi_pc_rdata == csr_mepc_if.rvfi_csr_rdata;
    endproperty : p_mret_pc_not_vectored_1

    a_mret_pc_not_vectored_1: assert property (p_mret_pc_not_vectored_1)
    else
      `uvm_error(info_tag,
        $sformatf("mret result state incorrect"));


    //mret to umode clears mintthresh
    a_mret_umode_clear_mintthresh: assert property (
      rvfi_if.is_mret
      //&& !rvfi_if.rvfi_trap.trap
      ##1 rvfi_valid[->1]
      ##0 rvfi_if.is_umode
      |->
      csr_mintthresh_if.rvfi_csr_rdata == 0
    )
    else
      `uvm_error(info_tag,
        $sformatf("mret to umode does not clear mintthresh"));



    property p_execution_state_after_mret;
     // last cycle after mret, before new rvfi_valid,
          // and not an excepted minhv-mepc (TODO: where? covered elsewhere)
        rvfi_if.is_mret
        && !rvfi_if.rvfi_trap.trap
        && !rvfi_mcause_fields.minhv
        ##1 rvfi_valid[->1]
      |->
        // 1. Standard behavior
        rvfi_if.rvfi_pc_rdata == csr_mepc_if.rvfi_csr_rdata
      or
        rvfi_if.rvfi_intr.intr
      or
        support_if.first_debug_ins

      /*
           // irq taken, mepc not written by retiring instruction
           // address checked by mtvec/mtvt assertions
           //irq_ack_occurred_between_valid
           rvfi_intr.intr
        && !(is_csr_write  == 1'b1
        && is_mepc_access_instr == 1'b1)

      or
           // irq taken, handler rewrites mepc
           // only check mepc update, irq dest. addr checked by respective assertions
           //irq_ack_occurred_between_valid
           rvfi_intr.intr
        && mepc_fields == rvfi_mepc_wdata & rvfi_mepc_wmask
        && is_csr_write  == 1'b1
        && is_mepc_access_instr == 1'b1
      or
           // debug gets taken, write effects of instruction on rvfi_valid should have no effect,
           // but there might be an instruction fault
           rvfi_dbg_mode == 1'b1
        && rvfi_pc_rdata == { debug_halt_addr[31:2], 2'b00 }
        && is_trap_exception
      or
           // Trap to debug and take exception
           rvfi_dbg_mode == 1'b1
        && rvfi_pc_rdata == { debug_exc_addr[31:2], 2'b00 }
        && is_intr_exception
      or
           // Trap to debug and take ecall/ebreak
           rvfi_dbg_mode == 1'b1
        && rvfi_pc_rdata == { debug_halt_addr[31:2], 2'b00 }
        && is_intr_ecall_ebreak

      or
           // Trap to debug
           rvfi_dbg_mode == 1'b1
        && rvfi_pc_rdata == { debug_halt_addr[31:2], 2'b00 }
        && !is_intr_exception
        && !is_trap_exception
      or
           // Write to mepc, need to check past mepc
           !irq_ack_occurred_between_valid
        && rvfi_pc_rdata == $past(mepc_fields)
        && is_csr_write  == 1'b1
        && is_mepc_access_instr == 1'b1
      or
           // nmi
           rvfi_pc_rdata == { mtvec_fields[31:2], 2'b00 } + NMI_OFFSET
        && is_cause_nmi  == 1'b1
      or
           // nmi with retired write to mtvec
           rvfi_pc_rdata == { $past(mtvec_fields[31:2]), 2'b00 } + NMI_OFFSET
        && is_cause_nmi  == 1'b1

      */
      ;
       // TODO add mpil, mpie
    endproperty : p_execution_state_after_mret

    // TODO:MT reenable after rebuild
    //a_execution_state_after_mret: assert property (p_execution_state_after_mret)
    //else
    //  `uvm_error(info_tag,
    //    $sformatf("mret result state incorrect"));

    property p_execution_state_after_mret_with_minhv;
      logic [3:0] pointer_req = '0;
      logic [31:0] pointer_value = '0;
      sync_accept_on(
           !$stable(mepc_fields, @(posedge clk_i))
        || is_csr_write && is_mcause_access_instr && $fell(mcause_fields.minhv, @(posedge clk_i))
      )
           rvfi_valid
        && is_trap_exception
        && mcause_fields.minhv
       ##0 ((obi_instr_addr == mepc_fields)[->1],
            pointer_req = obi_instr_request_n
       )
       ##1 ((pointer_req == obi_instr_service_n)[->1],
            pointer_value = obi_instr_rdata
       )
       ##0 (rvfi_valid && is_last_mret_instr && !rvfi_trap.exception)[->1]
       ##1 rvfi_valid[->1]
         |->
       rvfi_pc_rdata == pointer_value
      or
          is_instr_access_fault
       && mcause_fields.minhv == 1'b1;
    endproperty : p_execution_state_after_mret_with_minhv

    // TODO:MT reenable after rebuild
    //a_execution_state_after_mret_with_minhv: assert property (p_execution_state_after_mret_with_minhv)
    //else
    //  `uvm_error(info_tag,
    //    $sformatf("mret result state incorrect"));

    // ------------------------------------------------------------------------
    // clic level should be the larger of mintthresh_th and prev. taken irq
    // ------------------------------------------------------------------------
    uncompressed_instr_t last_valid_instr;
    csr_instr_t          last_valid_instr_csr;

    // Formal tools generate warnings for latch behavior in assign statements, use explicit always_latch here
    always_latch begin
      last_valid_instr <= !rst_ni ? '0 : rvfi_valid ? uncompressed_instr_t'(rvfi_insn) : last_valid_instr;
    end

    assign last_valid_instr_csr = csr_instr_t'(last_valid_instr); //TODO:MT not used?

    logic is_last_mret_instr;
    logic is_last_dret_instr;

    property p_last_valid_instr_reset_state;
        !fetch_enable |-> last_valid_instr == 'h0;
    endproperty : p_last_valid_instr_reset_state

    // Keep track of last retired instruction type
    assign is_last_mret_instr   = is_instr(last_valid_instr, MRET);
    assign is_last_dret_instr   = is_instr(last_valid_instr, DRET);

    function logic[7:0] max_level(logic[7:0] a, logic[7:0] b);
      max_level = a > b ? a : b;
    endfunction : max_level

    property p_clic_core_level_max_prev_irq_mintthresh_th;
      // Evaluates to true false on second cycle, thus the duality of
      // $past and present statements below. TODO: possible to simplify without leaving holes?
      1 ##1 // out of reset fix
      $changed(mintstatus_fields.mil)
      |->
          // first cycle ack, no mret, mpp machine mode
          $past(irq_ack)
       && !$past(is_mret_instr)
       && $past(mcause_fields.mpp) == M_MODE
       && mintstatus_fields.mil == clic_oic.level
       && clic_oic.level > max_level($past(mintthresh_fields.th), $past(mintstatus_fields.mil))
      or
         // first cycle ack, no mret, mpp user mode
          $past(irq_ack)
       && !$past(is_mret_instr)
       && $past(mcause_fields.mpp) == U_MODE
       && mintstatus_fields.mil == clic_oic.level
       && clic_oic.level > 0
      or
         // first cycle ack, no mret
         // mret sets mil to mpil, but at next rvfi_valid this is replaced by
         // the il of the taken interrupt
          $past(irq_ack)
       && $past(is_mret_instr)
       && mintstatus_fields.mil == mcause_fields.mpil
      ##1 mintstatus_fields.mil == clic_oic.level
      or
         // first cycle ack and mnxti write
         // mnxti updated mil with pending interrupt
         $past(irq_ack)
      && $past(is_valid_mnxti_write)
      && mintstatus_fields.mil == $past(clic.level, 3)
      ##1 mintstatus_fields.mil == clic_oic.level
       && clic_oic.level > max_level($past(mintthresh_fields.th), $past(mintstatus_fields.mil))
      or
          // first cycle ack, mret, mpp user mode
          $past(irq_ack)
       && $past(is_mret_instr)
       && $past(mcause_fields.mpp) == U_MODE
       && $past(mintstatus_fields.mil) == $past(mcause_fields.mpil)
      ##1 mintstatus_fields.mil > 0
       && clic_oic.level == mintstatus_fields.mil
      or
         // no taken interrupt and mret
         // mret updates mil to mpil
          !$past(irq_ack)
       && $past(is_mret_instr)
       && mintstatus_fields.mil == mcause_fields.mpil
      or
          // no taken interrupt but mnxti updated mil with pending interrupt
          is_valid_mnxti_write
       && mintstatus_fields.mil == $past(clic.level, 2)
      or
          // last instruction before taken interrupt is dret, with prv set to user mode
          // vertical interrupt handling
          (is_last_dret_instr || $past(is_dret_instr))
       && $past(irq_ack)
       && $past(dcsr_fields.prv) == U_MODE
      ##1 mintstatus_fields.mil > 0
       && clic_oic.level == mintstatus_fields.mil
      or
          // last instruction before taken interrupt is dret, with prv set to machine mode
          // horizontal interrupt handling
          (is_last_dret_instr || $past(is_dret_instr))
       && $past(irq_ack)
       && $past(dcsr_fields.prv) == M_MODE
      ##1 clic_oic.level > max_level($past(mintthresh_fields.th), $past(mintstatus_fields.mil))
       && clic_oic.level == mintstatus_fields.mil
      or
          // pure mret, no irq, no prior back to back instruction in wb
          is_mret_instr
       && !irq_ack
       && mintstatus_fields.mil == mcause_fields.mpil
      or
           // mret retire immediately prior to ack, with mpp machine mode
           irq_ack
       &&  is_mret_instr
       &&  mcause_fields.mpp == M_MODE
       &&  mintstatus_fields.mil == mcause_fields.mpil
      ##1  mintstatus_fields.mil == clic_oic.level
       &&  clic_oic.level > max_level($past(mintthresh_fields.th), $past(mintstatus_fields.mil))
      or
           // mret retire immediately prior to ack, with mpp user mode
           irq_ack
       &&  is_mret_instr
       &&  mcause_fields.mpp == U_MODE
       &&  mintstatus_fields.mil == mcause_fields.mpil
      ##1  mintstatus_fields.mil == clic_oic.level
       &&  clic_oic.level > 0
      or
          // something wrong happened and instruction trapped
          rvfi_valid[->1]
      ##0 rvfi_trap
      or
          // nmi occurred
          rvfi_valid[->1]
      ##0 is_cause_nmi
      ;
    endproperty : p_clic_core_level_max_prev_irq_mintthresh_th



    // TODO:MT reenable after rebuild
    //a_clic_core_level_max_prev_irq_mintthresh_th: assert property (p_clic_core_level_max_prev_irq_mintthresh_th)
    //else
    //  `uvm_error(info_tag,
    //    $sformatf("internal clic level error"));


     //// WIP section END ////

    // ------------------------------------------------------------------------
    // Horizontal exception handling
    // ------------------------------------------------------------------------

    property p_horizontal_exception_service;
            rvfi_mode == M_MODE
         && rvfi_valid
         && rvfi_trap.exception
      |->
        ##0 $stable(current_priv_mode,     @(posedge clk_i))
         && $stable(mintstatus_fields.mil, @(posedge clk_i))
      until_with rvfi_valid[->1];
    endproperty : p_horizontal_exception_service

    property p_stable_mode_lvl;
      $stable(current_priv_mode) && $stable(mintstatus_fields.mil);
    endproperty : p_stable_mode_lvl

    a_horizontal_exception_service: assert property (p_horizontal_exception_service)
    else
      `uvm_error(info_tag,
        $sformatf("Horizontal exception service not handled correctly"));

    // ------------------------------------------------------------------------
    // Vertical exception handling
    // ------------------------------------------------------------------------

    property p_vertical_exception_service;
            rvfi_valid
        &&  rvfi_trap.exception
        &&  rvfi_mode == U_MODE
        ##1 rvfi_valid[->1]
      |->
            // regular case
        ##0 mintstatus_fields.mil == 0
        &&  rvfi_mode == M_MODE
      or
            // mnxti overwriting expected mil, checked in mnxti assertions
        ##0 is_mnxti_access_instr
        &&  rvfi_mode == M_MODE
      or
            // first handler instruction is mret, should be handled at lvl 0,
            // but mpil may cause mil to change after mret retirement
        ##0 is_mret_instr
        &&  rvfi_mode == M_MODE
        &&  $past(mintstatus_fields.mil) == 0
        &&  mintstatus_fields.mil == $past(mcause_fields.mpil)
      ;
    endproperty : p_vertical_exception_service

    a_vertical_exception_service: assert property (p_vertical_exception_service)
    else
      `uvm_error(info_tag,
        $sformatf("Vertical exception service not handled correctly"));

    // ------------------------------------------------------------------------
    // MEPC lsb should always be 0
    // ------------------------------------------------------------------------
    property p_mepc_lsb_always_zero;
      mepc_fields.reserved == 1'b0;
    endproperty : p_mepc_lsb_always_zero;

    a_mepc_lsb_always_zero: assert property (p_mepc_lsb_always_zero)
    else
      `uvm_error(info_tag,
        $sformatf("mepc[0] should always be zero"));

    // ------------------------------------------------------------------------
    // Checks correct behavior of accesses to mscratchcsw
    // ------------------------------------------------------------------------
    // FIXME: Fails for undefined CSR instructions (needs defined behavior)
    property p_mscratchcsw_value;
           is_mscratchcsw_access_instr
        && csr_instr.funct3    == CSRRW
        && csr_instr.rd        != X0
        && csr_instr.n.rs1     != X0
      |->
           rvfi_rd_wdata       == (csr_instr.rd != X0 ? rvfi_mscratch_rdata : 'b0)
        && rvfi_mscratch_wdata == rvfi_rs1_rdata
        && mstatus_fields.mpp  != rvfi_mode
      or
           rvfi_rd_wdata       == rvfi_rs1_rdata
        && rvfi_mscratch_wmask == 'h0
        && mstatus_fields.mpp  == rvfi_mode
      or
           rvfi_trap.exception
      or
           rvfi_trap.debug
      ;
    endproperty : p_mscratchcsw_value

    a_mscratchcsw_value: assert property (p_mscratchcsw_value)
    else
      `uvm_error(info_tag,
        $sformatf("mscratchcsw value not as expected"));

    // ------------------------------------------------------------------------
    // Checks correct behavior of accesses to mscratchcswl
    // ------------------------------------------------------------------------
    // FIXME: Fails for undefined CSR instructions (needs defined behavior)
    property p_mscratchcswl_value;
           is_mscratchcswl_access_instr
        && csr_instr.funct3    == CSRRW
        && csr_instr.rd        != X0
        && csr_instr.n.rs1     != X0
      |->
           rvfi_rd_wdata       == (csr_instr.rd != X0 ? rvfi_mscratch_rdata : 'b0)
        && rvfi_mscratch_wdata == rvfi_rs1_rdata
        && |mcause_fields.mpil  ^ |mintstatus_fields.mil
      or
           rvfi_rd_wdata       == rvfi_rs1_rdata
        && rvfi_mscratch_wmask == 'h0
        && |mcause_fields.mpil ^~ |mintstatus_fields.mil
      or
           rvfi_trap.exception
      or
           rvfi_trap.debug
      ;
    endproperty : p_mscratchcswl_value

    a_mscratchcswl_value: assert property (p_mscratchcswl_value)
    else
      `uvm_error(info_tag,
        $sformatf("mscratchcswl value not as expected"));

    // ------------------------------------------------------------------------
    // Formal verification constraints
    // Gated due to some simulators not ignoring restrict keyword
    // ------------------------------------------------------------------------

    `ifdef FORMAL
      // Stability assumes
      r_fetch_enable_stable:                   restrict property (fetch_enable |-> $stable(mtvec_addr_i));
      r_clic_mode_assume:                      restrict property (p_clic_mode_only);
      r_irq_i:                                 restrict property (irq_i == 0);

      // prevents undefined latch value out of reset in formal
      r_last_valid_init_state:                 restrict property (p_last_valid_instr_reset_state);
      r_irq_ack_occurred_zero_out_of_of_reset: restrict property (p_irq_ack_occurred_zero_out_of_reset);

      // Sanity cover for mtvt table helper logic
      c_mtvt_table_read_equals_value_written:  cover property (p_mtvt_table_read_equals_value_written);
      r_mtvt_table_read_equals_value_written:  restrict property (p_mtvt_table_read_equals_value_written);

      //`define CLIC_DELAY_RESTRICTIONS
      `ifdef CLIC_DELAY_RESTRICTIONS // TODO: (silabs-hfegran) temporary fix, implement with tcl script later
      // These attempts to restrict the amount of bus-induced delays during formal analysis to help reach
      // a bounded proof, as in theory infinte bus stalls are possible.
      // Limit data and instr stalls for formal convergence, consider removing when assertion set matures
      r_instr_load_stalls:                     restrict property (p_obi_instr_max_load_stalls);
      r_instr_max_gnt_stalls:                  restrict property (p_obi_instr_max_gnt_stalls);
      r_data_load_stalls:                      restrict property (p_obi_data_max_load_stalls);
      r_data_max_gnt_stalls:                   restrict property (p_obi_data_max_gnt_stalls);
      `endif

    `endif

  end

  endgenerate
endmodule : uvmt_cv32e40s_clic_interrupt_assert

