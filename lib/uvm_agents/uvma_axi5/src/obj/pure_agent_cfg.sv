// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group


`ifndef __UVMA_AXI_CFG_SV__
`define __UVMA_AXI_CFG_SV__

/**
 * Object encapsulating all parameters for creating, connecting and running all
 * AXI agent (uvma_axi_agent_c) components.
 */
class uvma_axi_cfg_c extends uvm_object;

   rand uvm_active_passive_enum            is_active;
   rand bit                                is_slave;
   rand uvma_axi_dv_ver_t                  version;

   rand bit                                preload_mem;
   rand bit                                external_mem;
   rand bit                                pure_mode_agent;
   rand bit                                randomization_enabled;
   rand bit                                rand_channel_delay_enabled;
   rand bit                                cov_model_enabled;
   rand bit                                trn_log_enabled;
   rand uvma_axi_dv_driver_idle_t          driver_idle_value_cfg;

   rand bit                                axi_lock_enabled;
   rand bit                                axi_region_enabled;
   rand bit                                axi_prot_enabled;
   rand longint unsigned                   m_addr_start;
   rand longint unsigned                   m_addr_end;
   rand int                                m_num_part;
   rand int                                m_num_axi_region;

   rand uvma_axi_slv_drv_ordering_mode     ordering_read_mode;
   rand uvma_axi_slv_drv_ordering_mode     ordering_write_mode;
   rand int                                max_outstanding_write_trs;
   rand int                                max_outstanding_read_trs;
   rand int                                max_read_response_latency;
   rand int                                max_write_response_latency;

   uvma_axi_transaction_cfg_c              txn_config;

   typedef struct{
            rand longint  unsigned    m_part_addr_start;
            rand longint  unsigned    m_part_size;
            rand bit[1:0]     m_type_access;         //index 0 for read access ; index 1 for write access
            rand bit[2:0]     axi_prot_type_access;  // prot supported  index 0 for Privileged access ; index 1 for Secure access ; index 2 for data or instruction access
           } m_part_td;

   rand m_part_td m_part_st[];

   `uvm_object_utils_begin(uvma_axi_cfg_c)
      `uvm_field_enum  (uvm_active_passive_enum, is_active, UVM_DEFAULT);
      `uvm_field_int   (is_slave, UVM_DEFAULT)
      `uvm_field_int   (trn_log_enabled, UVM_DEFAULT)
      `uvm_field_int   (axi_lock_enabled, UVM_DEFAULT)
      `uvm_field_int   (cov_model_enabled, UVM_DEFAULT)
      `uvm_field_int   (randomization_enabled, UVM_DEFAULT)
      `uvm_field_int   (rand_channel_delay_enabled, UVM_DEFAULT)
      `uvm_field_enum  (uvma_axi_slv_drv_ordering_mode, ordering_read_mode, UVM_DEFAULT);
      `uvm_field_enum  (uvma_axi_slv_drv_ordering_mode, ordering_write_mode, UVM_DEFAULT);
      `uvm_field_int   (max_outstanding_write_trs, UVM_DEFAULT)
      `uvm_field_int   (max_outstanding_read_trs, UVM_DEFAULT)
      `uvm_field_int   (max_read_response_latency, UVM_DEFAULT)
      `uvm_field_int   (max_write_response_latency, UVM_DEFAULT)
      `uvm_field_int   (axi_region_enabled, UVM_DEFAULT)
      `uvm_field_int   (axi_prot_enabled, UVM_DEFAULT)
      `uvm_field_int   (m_addr_start, UVM_DEFAULT)
      `uvm_field_int   (m_addr_end, UVM_DEFAULT)
      `uvm_field_int   (m_num_part, UVM_DEFAULT)
      `uvm_field_int   (m_num_axi_region, UVM_DEFAULT)
      `uvm_field_enum  (uvma_axi_dv_ver_t, version, UVM_DEFAULT);
      `uvm_field_int   (preload_mem, UVM_DEFAULT)
      `uvm_field_int   (external_mem, UVM_DEFAULT)
      `uvm_field_int   (pure_mode_agent, UVM_DEFAULT)
      `uvm_field_object(txn_config, UVM_DEFAULT)
      `uvm_field_enum  (uvma_axi_dv_driver_idle_t , driver_idle_value_cfg   , UVM_DEFAULT)
   `uvm_object_utils_end

   constraint defaults_config {
      soft is_active                   == UVM_ACTIVE;
      soft is_slave                    == 1;
      soft trn_log_enabled             == 1;
      soft axi_lock_enabled            == 1;
      soft cov_model_enabled           == 1;
      soft version                     == AXI5;
      soft axi_region_enabled          == 0;
      soft axi_prot_enabled            == 0;
      soft preload_mem                 == 0;
      soft pure_mode_agent             == 1;
      soft driver_idle_value_cfg       == RANDOM;
     }

   constraint pure_config {
      if(pure_mode_agent) {
         randomization_enabled       == 0;
         rand_channel_delay_enabled  == 0;
         ordering_read_mode          == UVMA_AXI_ORDERING_MODE_RANDOM;
         ordering_write_mode         == UVMA_AXI_OUTSTANDING_MODE;
         max_outstanding_write_trs   == 0;
         max_outstanding_read_trs    == 0;
         max_write_response_latency  == 0;
         max_read_response_latency   == 0;
         external_mem                == 1;
      } else {
         randomization_enabled       == 0;
         rand_channel_delay_enabled  == 0;
         ordering_read_mode          == UVMA_AXI_ORDERING_MODE_RANDOM;
         ordering_write_mode         == UVMA_AXI_OUTSTANDING_MODE;
         max_outstanding_write_trs   == 2;
         max_outstanding_read_trs    == 2;
         max_write_response_latency  == 15;
         max_read_response_latency   == 15;
         external_mem                == 0;
      }
     }
  

   // Number of RAM partitions
   constraint part_numb_const {
                               if(axi_region_enabled){
                                  m_num_part == m_num_axi_region;
                                  m_num_part <= 16;
                               } else
                                  m_num_part < 20;
                              }

   // Start addr of each partition
   constraint part_const { m_part_st.size() == m_num_part;
                           m_part_st[0].m_part_addr_start == m_addr_start;
                         }

   // Size of each partition
   constraint part_size_const {foreach (m_part_st[i]) {
                                  if(i == m_part_st.size()-1)
                                     m_part_st[i].m_part_size == m_addr_end - m_part_st[i].m_part_addr_start;
                                  else
                                     m_part_st[i].m_part_size == m_part_st[i+1].m_part_addr_start - m_part_st[i].m_part_addr_start;
                               }
                               foreach (m_part_st[i]) {
                                  m_part_st[i].m_part_size inside {[32768:m_addr_end]};
                               }
                              }

   //ACCESS TYPE for each partition
   constraint part_access { if(!axi_prot_enabled){
                              foreach (m_part_st[i]) {
                                  m_part_st[i].axi_prot_type_access == 0;
                              }
                           }
                         }

   /**
   * Default constructor.
   */
   extern function new(string name = "uvma_axi_cfg");

endclass : uvma_axi_cfg_c

function uvma_axi_cfg_c::new(string name = "uvma_axi_cfg");

   super.new(name);
   txn_config = uvma_axi_transaction_cfg_c::type_id::create("txn_config");

endfunction : new

`endif //__UVMA_AXI_CFG_SV__
