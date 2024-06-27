// ----------------------------------------------------------------------------
// Copyright 2023 CEA*
// *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//[END OF HEADER]
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//  Description : Module with the register adapter for the agent
// ----------------------------------------------------------------------------

// -----------------------------------------------------------------------
// Class axi_superset_reg_adapter_c
//
// Module which convert the uvm_register accesses into axi transactions
// -----------------------------------------------------------------------
class axi_superset_reg_adapter_c #( type T = int ) extends uvm_reg_adapter ;

  `uvm_object_param_utils( axi_superset_reg_adapter_c #(T) )

  // ------------------------------------------------------------------------
  // Local variable
  // ------------------------------------------------------------------------
  protected string  name ;
  axi_superset_txn_cfg_c  m_txn_config ;

  // ------------------------------------------------------------------------
  // Constructor
  // ------------------------------------------------------------------------
  function new(string name = "axi4_reg_adapter");
    super.new(name);
    this.name = name;

    supports_byte_enable = 0;
    provides_responses = 1;

  endfunction

  // ------------------------------------------------------------------------
  // Function: reg2bus
  //
  // This converts the reg items to AXI bus specific items. 
  // ------------------------------------------------------------------------
  virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
    axi_sig_addr_t  aligned_addr   ;
    axi_sig_addr_t  unaligned_addr ;

    // Creating the transaction
    T axi_txn = T::type_id::create("axi4");

    // Getting the register map
    uvm_reg_item       item = get_item();
    uvm_sequencer_base seqr = item.map.get_sequencer();

    // Getting the transaction configuration from the sequencer
    axi_txn.set_config( m_txn_config ) ;
    axi_txn.set_sequencer(seqr);

    // Randomizing the transaction depending of the register access
    if (rw.kind == UVM_WRITE) begin
      if (!axi_txn.randomize() with {
        m_axi_version == AXI4                                        ;
        m_txn_type    == AXI_WRITE_REQ                               ;
        m_addr        == rw.addr[31:0]                               ;
        m_len         == 0                                           ;
        2**m_size     == ( rw.n_bits + 8 - 1 )/8                     ;
        m_burst       == INCR                                        ;
        foreach ( m_data[i]  ) m_data[i] == rw.data                  ;
        m_prot     == UNPRIVILEGED_SECURE_DATA_ACCESS                ;
        m_region   == 0                                              ;
        m_qos      == 0                                              ;
        m_delay_cycle_chan_X == 0                                    ;
        m_delay_cycle_chan_W == m_delay_cycle_chan_X                 ;
        foreach (m_delay_cycle_flits[i]) m_delay_cycle_flits[i] <= 1 ;
      } )
        `uvm_fatal("reg2bus","bad constraints in UVM_WRITE")

      // Generating a write strobe corresponding to the register access, in
      // case of unaligned accesses
      axi_txn.m_wstrb[0] = rw.byte_en;
      for ( int j = $size(axi_txn.m_wstrb[0]) ; j > 0 ; j-- ) begin
        if ( $countones(axi_txn.m_wstrb[0]) > 2**axi_txn.m_size ) 
          axi_txn.m_wstrb[0][j] = 0 ;
      end
      // Aligning the data/write strobe, in case of unaligned accesses
      axi_txn.m_data[0]  = axi_txn.m_data[0]  << ( ( axi_txn.m_addr % ( m_txn_config.get_data_width() / 8 ) ) * 8);
      axi_txn.m_wstrb[0] = axi_txn.m_wstrb[0] << ( axi_txn.m_addr % ( m_txn_config.get_data_width() / 8 ) );

    end else begin
      if (!axi_txn.randomize() with {
        m_axi_version == AXI4                                ;
        m_txn_type    == AXI_READ_REQ                        ;
        m_addr        == rw.addr[31:0]                       ;
        m_len         == 0                                   ;
        2**m_size     == ( rw.n_bits + 8 - 1 ) / 8           ;
        m_burst       == INCR                                ;
        m_prot        == UNPRIVILEGED_SECURE_DATA_ACCESS     ;
        m_region      == 0                                   ;
        m_qos         == 0                                   ;
        m_delay_cycle_chan_X == 0                                    ;
        m_delay_cycle_chan_W == m_delay_cycle_chan_X                 ;
        foreach (m_delay_cycle_flits[i]) m_delay_cycle_flits[i] <= 1 ;
      } )
        `uvm_fatal("reg2bus","bad constraints in UVM_READ")
    end

    // Some debug messages
    `uvm_info("reg2bus",$sformatf("do register access: %p",rw),UVM_DEBUG)
    `uvm_info( this.name, $sformatf("REQ, Info: %0s", axi_txn.convert2string()) , UVM_DEBUG)

    return axi_txn;
  endfunction: reg2bus

  // ------------------------------------------------------------------------
  // Function: bus2reg
  //
  // This converts the AXI4 bus specific items to reg items. 
  // ------------------------------------------------------------------------
  virtual function void bus2reg(uvm_sequence_item bus_item,
                                ref uvm_reg_bus_op rw);
    T axi_txn;

    // Casting the transaction to get it
    if (!$cast(axi_txn, bus_item)) begin
      `uvm_fatal("NOT_AXI4_TYPE","Provided bus_item is not of the correct type")
      return;
    end

    // Print information about the transaction
    `uvm_info( this.name, $sformatf("RSP, Info: %0s", axi_txn.convert2string()) , UVM_DEBUG)

    // Aligning the data in case of unaligned accesses
    rw.data   = axi_txn.m_data[0] >> ( ( axi_txn.m_addr % ( m_txn_config.get_data_width() / 8 ) ) * 8);
    rw.kind   = (axi_txn.m_txn_type == AXI_WRITE_RSP) ? UVM_WRITE : UVM_READ;
    rw.addr   = axi_txn.m_addr;
    rw.n_bits = m_txn_config.get_data_width();

    // Check if we received an error or not from the accesses
    rw.status = UVM_IS_OK;
    if(axi_txn.m_resp[0] != OKAY)
      rw.status = UVM_NOT_OK;

    `uvm_info("bus2reg", $sformatf("saw register access: %p",rw), UVM_DEBUG)
  endfunction: bus2reg

  // CONFIGURATION
  function axi_superset_txn_cfg_c get_config();
    get_config = m_txn_config  ;
  endfunction : get_config

  function void set_config( axi_superset_txn_cfg_c config_i );
    `uvm_info("SET_TXN_CONFIG",$sformatf("New config %0s", config_i.convert2string() ), UVM_DEBUG)
    m_txn_config = config_i ;
  endfunction: set_config

endclass: axi_superset_reg_adapter_c

