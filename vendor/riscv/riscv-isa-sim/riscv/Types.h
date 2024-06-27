#pragma once

#include <fesvr/htif.h>
#include <vector>
#include <map>
#include <string>
#include <memory>
#include <thread>
#include <sys/types.h>
#include "Params.h"

#define CSR_MAX_SIZE 4096

typedef struct {
   uint64_t                 nret_id;
   uint64_t                 cycle_cnt;
   uint64_t                 order;
   uint64_t                 insn;
   uint64_t                 trap;
   uint64_t                 halt;
   uint64_t                 intr;
   uint64_t                 mode;
   uint64_t                 ixl;
   uint64_t                 dbg;
   uint64_t                 dbg_mode;
   uint64_t                 nmip;

   uint64_t                 insn_interrupt;
   uint64_t                 insn_interrupt_id;
   uint64_t                 insn_bus_fault;
   uint64_t                 insn_nmi_store_fault;
   uint64_t                 insn_nmi_load_fault;

   uint64_t                 pc_rdata;
   uint64_t                 pc_wdata;

   uint64_t                 rs1_addr;
   uint64_t                 rs1_rdata;

   uint64_t                 rs2_addr;
   uint64_t                 rs2_rdata;

   uint64_t                 rs3_addr;
   uint64_t                 rs3_rdata;

   uint64_t                 rd1_addr;
   uint64_t                 rd1_wdata;

   uint64_t                 rd2_addr;
   uint64_t                 rd2_wdata;

   uint64_t                 mem_addr;
   uint64_t                 mem_rdata;
   uint64_t                 mem_rmask;
   uint64_t                 mem_wdata;
   uint64_t                 mem_wmask;

   uint64_t                 csr_valid   [CSR_MAX_SIZE];
   uint64_t                 csr_addr    [CSR_MAX_SIZE];
   uint64_t                 csr_rdata   [CSR_MAX_SIZE];
   uint64_t                 csr_rmask   [CSR_MAX_SIZE];
   uint64_t                 csr_wdata   [CSR_MAX_SIZE];
   uint64_t                 csr_wmask   [CSR_MAX_SIZE];

} st_rvfi;


