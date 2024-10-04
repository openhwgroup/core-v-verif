// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group


`ifndef __UVMA_AXI_FW_PRELOAD_SEQ_SV__
`define __UVMA_AXI_FW_PRELOAD_SEQ_SV__


/**
 * Virtual sequence preload memory.
 */
class uvma_axi_fw_preload_seq_c extends uvm_sequence;

   // Agent handles
   uvma_axi_cfg_c    cfg;
   uvma_axi_cntxt_c  cntxt;

   string fw_file_path;

   `uvm_object_utils(uvma_axi_fw_preload_seq_c)
   `uvm_declare_p_sequencer(uvma_axi_vsqr_c)

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_axi_fw_preload_seq");

   extern virtual task body();

endclass : uvma_axi_fw_preload_seq_c

function uvma_axi_fw_preload_seq_c::new(string name="uvma_axi_fw_preload_seq");

   super.new(name);

endfunction : new

task uvma_axi_fw_preload_seq_c::body();

   if ($value$plusargs("firmware=%s", fw_file_path)) begin
      cntxt.mem.readmemh(fw_file_path);
   end

endtask : body

`endif // __UVMA_AXI_FW_PRELOAD_SEQ_SV__
