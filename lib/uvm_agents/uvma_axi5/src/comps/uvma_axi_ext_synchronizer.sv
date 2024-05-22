// Copyright 2023 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group


`ifndef __UVMA_AXI_EXT_SYNCHRONIZER_SV__
`define __UVMA_AXI_EXT_SYNCHRONIZER_SV__

/**
 * TODO Describe uvma_axi_ext_synchronizer_c
 */
class uvma_axi_ext_synchronizer_c extends uvma_axi_amo_synchronizer_c;

   `uvm_component_utils(uvma_axi_ext_synchronizer_c)

   int  outstanding_read_call_times  = 0;
   int  outstanding_write_call_times = 0;

   /**
    * Default constructor.
    */
   extern function new(string name = "uvma_axi_ext_synchronizer", uvm_component parent);

   /**
    * 1. Ensures cntxt handles are not null
    * 2. Builds all components
    */
   extern function void build_phase(uvm_phase phase);

   /**
    * Method to select the Write ID from a table
    */
   extern function int w_select_id(int tab[]);

   /**
    * Method to select the READ ID from a table
    */
   extern function int r_select_id(int tab[]);

   /**
   * check the memory region attribute for each access to a memory location
   */
   extern function int check_memory_access(uvma_axi_base_seq_item_c item, uvma_axi_access_type_enum type_access);

endclass : uvma_axi_ext_synchronizer_c

function uvma_axi_ext_synchronizer_c::new(string name="uvma_axi_ext_synchronizer", uvm_component parent);

   super.new(name, parent);

endfunction : new

function void uvma_axi_ext_synchronizer_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

endfunction

function int uvma_axi_ext_synchronizer_c::w_select_id(int tab[]);

   int selected;
   int ind_slct;
   case (cfg.ordering_write_mode)
      UVMA_AXI_ORDERING_MODE_RANDOM : begin
         if(tab.size() == cfg.max_outstanding_write_trs) begin
            ind_slct = $urandom_range(0, tab.size() - 1);
            selected = tab[ind_slct];
            outstanding_write_call_times = 0;
         end else begin
            selected = -1;
            if(tab.size() < cfg.max_outstanding_write_trs && tab.size() != 0) begin
               outstanding_write_call_times++;
               if(outstanding_write_call_times == cfg.write_response_latency) begin
                  selected = tab[0];
                  outstanding_write_call_times = 0;
               end
            end
         end
      end
      UVMA_AXI_OUTSTANDING_MODE : begin

         if(tab.size() == cfg.max_outstanding_write_trs) begin

            `uvm_info(get_type_name(), $sformatf("double transaction ready"), UVM_HIGH)
            outstanding_write_call_times = 0;
            selected = tab[0];

         end else begin

            selected = -1;
            if(tab.size() < cfg.max_outstanding_write_trs && tab.size() != 0) begin
               outstanding_write_call_times++;
               if(outstanding_write_call_times == cfg.write_response_latency) begin
                  selected = tab[0];
                  outstanding_write_call_times = 0;
               end
            end

         end
      end

      UVMA_AXI_ORDERING_MODE_FIFO : begin

         selected = -1;
         if (tab.size() > 0) begin
            selected = tab[0];
         end

      end
   endcase
   return selected;

endfunction : w_select_id

function int uvma_axi_ext_synchronizer_c::r_select_id(int tab[]);

   int selected;
   int ind_slct;
   case (cfg.ordering_read_mode)
      UVMA_AXI_ORDERING_MODE_RANDOM : begin
         if(tab.size() == cfg.max_outstanding_read_trs) begin
            ind_slct = $urandom_range(0, tab.size() - 1);
            selected = tab[ind_slct];
            outstanding_read_call_times = 0;
         end else begin
            selected = -1;
            if(tab.size() < cfg.max_outstanding_read_trs && tab.size() != 0) begin
               outstanding_read_call_times++;
               if(outstanding_read_call_times == cfg.read_response_latency) begin
                  selected = tab[0];
                  outstanding_read_call_times = 0;
               end
            end
         end
      end

      UVMA_AXI_OUTSTANDING_MODE : begin

         if(tab.size() == cfg.max_outstanding_read_trs) begin

            `uvm_info(get_type_name(), $sformatf("double transaction ready"), UVM_HIGH)
            outstanding_read_call_times = 0;
            selected = tab[0];

         end else begin
            `uvm_info(get_type_name(), $sformatf("write_response_latency", cfg.read_response_latency), UVM_HIGH)
            selected = -1;
            if(tab.size() < cfg.max_outstanding_read_trs && tab.size() != 0) begin

               `uvm_info(get_type_name(), $sformatf("one transaction ready"), UVM_HIGH)
               outstanding_read_call_times++;
               if(outstanding_read_call_times == cfg.read_response_latency) begin
                  selected = tab[0];
                  outstanding_read_call_times = 0;
               end

            end
         end
      end

      UVMA_AXI_ORDERING_MODE_FIFO : begin
         selected = -1;
         if (tab.size() != 0) begin
            selected = tab[0];
         end
      end
   endcase
   `uvm_info(get_type_name(), $sformatf("outstanding_call_tims = %d",outstanding_write_call_times), UVM_HIGH)
   return selected;

endfunction : r_select_id

function int uvma_axi_ext_synchronizer_c::check_memory_access(uvma_axi_base_seq_item_c item, uvma_axi_access_type_enum type_access);

   int access      = 1;
   bit prot_access = 1;
   bit m_access    = 1;
   int trs_access  = 1;
   int region_index;

   case (type_access)
      UVMA_AXI_ACCESS_WRITE  : begin

         foreach(access_w_trs[i]) begin
            if(i == item.aw_id) begin
               trs_access = access_w_trs[i][0];
               break;
            end
         end

         if(cfg.axi_region_enabled) begin
            m_access = cfg.m_part_st[item.aw_region].m_type_access[1];
            if(cfg.axi_prot_enabled) begin
               prot_access = cfg.m_part_st[item.aw_region].axi_prot_type_access && item.aw_prot;
            end
         end else begin
            foreach(cfg.m_part_st[i]) begin
               if( i == cfg.m_part_st.size() -1) begin
                  if(cfg.m_part_st[i].m_part_addr_start <= item.aw_addr && cfg.m_addr_end > item.aw_addr) begin
                     region_index = i;
                     break;
                  end
               end else begin
                  if(cfg.m_part_st[i].m_part_addr_start <= item.aw_addr && cfg.m_part_st[i+1].m_part_addr_start > item.aw_addr) begin
                     region_index = i;
                     break;
                  end
               end
            end
            m_access = cfg.m_part_st[region_index].m_type_access[1];
            if(cfg.axi_prot_enabled) begin
               prot_access = cfg.m_part_st[region_index].axi_prot_type_access && item.aw_prot;
            end
         end

      end

      UVMA_AXI_ACCESS_READ  : begin

         foreach(access_r_trs[i]) begin
            if(i == item.ar_id) begin
               trs_access = access_r_trs[i][0];
               break;
            end
         end

         if(cfg.axi_region_enabled) begin
            m_access = cfg.m_part_st[item.ar_region].m_type_access[0];
            if(cfg.axi_prot_enabled) begin
               prot_access = cfg.m_part_st[item.ar_region].axi_prot_type_access && item.ar_prot;
            end
         end else begin
            foreach(cfg.m_part_st[i]) begin
               if( i == cfg.m_part_st.size() -1) begin
                  if(cfg.m_part_st[i].m_part_addr_start <= item.ar_addr && cfg.m_addr_end > item.ar_addr) begin
                     region_index = i;
                     break;
                  end
               end else begin
                  if(cfg.m_part_st[i].m_part_addr_start <= item.ar_addr && cfg.m_part_st[i+1].m_part_addr_start > item.ar_addr) begin
                     region_index = i;
                     break;
                  end
               end
            end
            m_access = cfg.m_part_st[region_index].m_type_access[0];
            if(cfg.axi_prot_enabled) begin
               prot_access = cfg.m_part_st[region_index].axi_prot_type_access && item.ar_prot;
            end
         end

      end
   endcase

   access = m_access && prot_access;

   if(access == 0) begin
      return -1;
   end else begin
      if(trs_access == 1) begin
         return 1;
      end else begin
         return 0;
      end
   end

endfunction : check_memory_access

`endif // __UVMA_AXI_EXT_SYNCHRONIZER_SV__
