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
   rand bit                                resp_randomization_enabled;
   rand bit                                user_randomization_enabled;
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
   rand bit                                zero_delay_mode;
   rand bit                                disable_trs_randomization;

   // Master configuration 
   uvma_axi_dv_lite_t      axi_lite                ;
   string                  interface_name          ;
   bit                     is_reactive             ;
   bit                     id_management_enable    ;
   bit                     covergroup_enable       ;


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
      `uvm_field_int   (resp_randomization_enabled, UVM_DEFAULT)
      `uvm_field_int   (user_randomization_enabled, UVM_DEFAULT)
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
      `uvm_field_int   (zero_delay_mode, UVM_DEFAULT)
      `uvm_field_int   (disable_trs_randomization, UVM_DEFAULT)
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
      pure_mode_agent                  == 0;
      soft zero_delay_mode             == 0;
      soft max_outstanding_write_trs   == 2;
      soft max_outstanding_read_trs    == 2;
      soft max_write_response_latency  == 15;
      soft max_read_response_latency   == 15;
      soft driver_idle_value_cfg       == RANDOM;
      soft disable_trs_randomization   == 0;
     }

   constraint pure_config {
      if(pure_mode_agent) {
         soft resp_randomization_enabled  == 0;
         soft user_randomization_enabled  == 0;
         soft rand_channel_delay_enabled  == 0;
         soft ordering_read_mode          == UVMA_AXI_ORDERING_MODE_FIFO;
         soft ordering_write_mode         == UVMA_AXI_ORDERING_MODE_FIFO;
         soft external_mem                == 1;
      } else {
         soft resp_randomization_enabled  == 0;
         soft user_randomization_enabled  == 0;
         soft rand_channel_delay_enabled  == 1;
         soft ordering_read_mode          == UVMA_AXI_ORDERING_MODE_RANDOM;
         soft ordering_write_mode         == UVMA_AXI_OUTSTANDING_MODE;
         soft external_mem                == 0;
      }
     }

     constraint delay_mode_c {
      if(zero_delay_mode) {
         rand_channel_delay_enabled  == 0;
         ordering_read_mode          == UVMA_AXI_ORDERING_MODE_FIFO;
         ordering_write_mode         == UVMA_AXI_ORDERING_MODE_FIFO;
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

   // -----------------------------------------------------------------------
   // AXI version
   // -----------------------------------------------------------------------
   extern function void set_axi_version( uvma_axi_dv_ver_t new_axi_version );
   
   extern function uvma_axi_dv_ver_t get_axi_version( );
   
   // -----------------------------------------------------------------------
   // AXI Lite version
   // -----------------------------------------------------------------------
   extern function void set_axi_lite( uvma_axi_dv_lite_t new_axi_lite );
   
   extern function uvma_axi_dv_lite_t get_axi_lite( );
   
   // -----------------------------------------------------------------------
   // Interface name
   // -----------------------------------------------------------------------
   extern function void set_interface_name( string interface_name );
   
   extern function string get_interface_name( );

   // -----------------------------------------------------------------------
   // uvma_axi_cfg_c::set/Get idle value tasks
   // -----------------------------------------------------------------------
   extern function void set_driver_idle_value_cfg( uvma_axi_dv_driver_idle_t driver_idle_value_cfg );
   
   extern function uvma_axi_dv_driver_idle_t get_driver_idle_value_cfg( );
   
   // TXN CONFIGURATION
   extern function uvma_axi_transaction_cfg_c get_txn_config();
   
   extern function void set_txn_config( uvma_axi_transaction_cfg_c config_i );

   // -----------------------------------------------------------------------
   // Master/Slave
   // -----------------------------------------------------------------------
   extern function void set_is_master_side( bit master_side );
   
   extern function bit get_is_master_side( );

   // -----------------------------------------------------------------------
   // id_management_enable
   // -----------------------------------------------------------------------
   extern function void set_id_management_enable( bit management_enable );
   
   extern function bit get_id_management_enable( );
endclass : uvma_axi_cfg_c

function uvma_axi_cfg_c::new(string name = "uvma_axi_cfg");

   super.new(name);
   txn_config = uvma_axi_transaction_cfg_c::type_id::create("txn_config");

endfunction : new

// -----------------------------------------------------------------------
// AXI version
// -----------------------------------------------------------------------
function void uvma_axi_cfg_c::set_axi_version( uvma_axi_dv_ver_t new_axi_version );
  version = new_axi_version;
endfunction: set_axi_version

function uvma_axi_dv_ver_t uvma_axi_cfg_c::get_axi_version( );
  return version;
endfunction: get_axi_version


// -----------------------------------------------------------------------
// AXI Lite version
// -----------------------------------------------------------------------
function void uvma_axi_cfg_c::set_axi_lite( uvma_axi_dv_lite_t new_axi_lite );
  axi_lite = new_axi_lite;
endfunction: set_axi_lite

function uvma_axi_dv_lite_t uvma_axi_cfg_c::get_axi_lite( );
  return axi_lite;
endfunction: get_axi_lite

// -----------------------------------------------------------------------
// Interface name
// -----------------------------------------------------------------------
function void uvma_axi_cfg_c::set_interface_name( string interface_name );
    interface_name = interface_name;
endfunction

function string uvma_axi_cfg_c::get_interface_name( );
    return interface_name;
endfunction

// -----------------------------------------------------------------------
// uvma_axi_cfg_c::set/Get idle value tasks
// -----------------------------------------------------------------------
function void uvma_axi_cfg_c::set_driver_idle_value_cfg( uvma_axi_dv_driver_idle_t driver_idle_value_cfg );
  driver_idle_value_cfg = driver_idle_value_cfg ;
endfunction: set_driver_idle_value_cfg

function uvma_axi_dv_driver_idle_t uvma_axi_cfg_c::get_driver_idle_value_cfg( );
  return driver_idle_value_cfg;
endfunction: get_driver_idle_value_cfg

// TXN CONFIGURATION
function uvma_axi_transaction_cfg_c uvma_axi_cfg_c::get_txn_config();
  if ( txn_config == null )
    `uvm_fatal("NO_TXN_CONFIG",
      $sformatf("The agent was not given any transaction configuration. The user should use create its own transaction configuration when configuring the agent, and use the function uvma_axi_cfg_c::set_txn_config to uvma_axi_cfg_c::set the transaction configuration in the agent configuration ") )
  return txn_config  ;
endfunction : get_txn_config

function void uvma_axi_cfg_c::set_txn_config( uvma_axi_transaction_cfg_c config_i );
  txn_config =  config_i ;
endfunction: set_txn_config


// -----------------------------------------------------------------------
// Master/Slave
// -----------------------------------------------------------------------
function void uvma_axi_cfg_c::set_is_master_side( bit master_side );
  is_slave = ~master_side;
endfunction: set_is_master_side

function bit uvma_axi_cfg_c::get_is_master_side( );
  return ~is_slave;
endfunction: get_is_master_side


// -----------------------------------------------------------------------
// id_management_enable
// -----------------------------------------------------------------------
function void uvma_axi_cfg_c::set_id_management_enable( bit management_enable );
  id_management_enable = management_enable;
endfunction: set_id_management_enable

function bit uvma_axi_cfg_c::get_id_management_enable( );
  return id_management_enable;
endfunction: get_id_management_enable

`endif //__UVMA_AXI_CFG_SV__
