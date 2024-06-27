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
//  Description : Configuration of the axi transaction fields
//
// ----------------------------------------------------------------------------

// ----------------------------------------------------------------------------
// Class uvma_axi_transaction_cfg_c
//
// This class contains the fields necessary to configure the oversized fields
// of the axi_superset_txn_c class.
//
// The fields are protected and may only be accessed by using the set/get
// function of the class.
//
// ----------------------------------------------------------------------------

`ifndef UVMA_AXI_TRANSACTION_CFG_SV
`define UVMA_AXI_TRANSACTION_CFG_SV

class uvma_axi_transaction_cfg_c extends uvm_object;

    protected string name;

    // -----------------------------------------------------------------------
    // Fields width configurable
    // -----------------------------------------------------------------------
    protected int unsigned m_id_width      ;
    protected int unsigned m_addr_width    ;
    protected int unsigned m_data_width    ;
    protected int unsigned m_user_width    ;
    protected int unsigned m_loop_width    ;
    protected int unsigned m_mmusid_width  ;
    protected int unsigned m_mmussid_width ;

    protected int unsigned m_max_delay_cycles ;
    protected int unsigned m_max_channel_delay_cycles ;

    // ------------------------------------------------------------------------
    // Utility/fields macros
    // ------------------------------------------------------------------------
    `uvm_object_utils_begin(uvma_axi_transaction_cfg_c)
        `uvm_field_int ( m_id_width                 , UVM_DEC )
        `uvm_field_int ( m_addr_width               , UVM_DEC )
        `uvm_field_int ( m_data_width               , UVM_DEC )
        `uvm_field_int ( m_user_width               , UVM_DEC )
        `uvm_field_int ( m_loop_width               , UVM_DEC )
        `uvm_field_int ( m_mmusid_width             , UVM_DEC )
        `uvm_field_int ( m_mmussid_width            , UVM_DEC )
        `uvm_field_int ( m_max_delay_cycles         , UVM_DEC )
        `uvm_field_int ( m_max_channel_delay_cycles , UVM_DEC )
    `uvm_object_utils_end

    // -----------------------------------------------------------------------
    // Functions/tasks
    // -----------------------------------------------------------------------
    // ID
    function void set_id_width( int unsigned new_id_width );
      `uvm_info($sformatf("%0s_CONFIG_ID", this.name), $sformatf("NEW_CFG_ID=%0d(d)", new_id_width), UVM_DEBUG);
      m_id_width = new_id_width;
    endfunction: set_id_width

    function int unsigned get_id_width( );
      get_id_width = m_id_width;
    endfunction: get_id_width

    // ADDR
    function void set_addr_width( int unsigned new_addr_width );
      `uvm_info($sformatf("%0s_CONFIG_ADDR", this.name), $sformatf("NEW_CFG_ADDR=%0d(d)", new_addr_width), UVM_DEBUG);
      m_addr_width = new_addr_width;
    endfunction :set_addr_width

    function int unsigned get_addr_width( );
      get_addr_width = m_addr_width;
    endfunction :get_addr_width

    // DATA
    function void set_data_width( int unsigned new_data_width );
      `uvm_info($sformatf("%0s_CONFIG_DATA", this.name), $sformatf("NEW_CFG_DATA=%0d(d)", new_data_width), UVM_DEBUG);
      m_data_width = new_data_width;
    endfunction :set_data_width

    function int unsigned get_data_width( );
      get_data_width = m_data_width;
    endfunction :get_data_width

    // USER
    function void set_user_width( int unsigned new_user_width );
      `uvm_info($sformatf("%0s_CONFIG_USER", this.name), $sformatf("NEW_CFG_USER=%0d(d)", new_user_width), UVM_DEBUG);
      m_user_width = new_user_width;
    endfunction :set_user_width

    function int unsigned get_user_width( );
      get_user_width = m_user_width;
    endfunction :get_user_width

    // LOOP
    function void set_loop_width( int unsigned new_loop_width );
      `uvm_info($sformatf("%0s_CONFIG_LOOP", this.name), $sformatf("NEW_CFG_LOOP=%0d(d)", new_loop_width), UVM_DEBUG);
      m_loop_width = new_loop_width;
    endfunction :set_loop_width

    function int unsigned get_loop_width( );
      get_loop_width = m_loop_width;
    endfunction :get_loop_width

    // MMUSID
    function void set_mmusid_width( int unsigned new_mmusid_width );
      `uvm_info($sformatf("%0s_CONFIG_MMUSID", this.name), $sformatf("NEW_CFG_MMUSID=%0d(d)", new_mmusid_width), UVM_DEBUG);
      m_mmusid_width = new_mmusid_width;
    endfunction :set_mmusid_width

    function int unsigned get_mmusid_width( );
      get_mmusid_width = m_mmusid_width;
    endfunction :get_mmusid_width

    // MMUSSID
    function void set_mmussid_width( int unsigned new_mmussid_width );
     `uvm_info($sformatf("%0s_CONFIG_MMUSSID", this.name), $sformatf("NEW_CFG_MMUSSID=%0d(d)", new_mmussid_width), UVM_DEBUG);
      m_mmussid_width = new_mmussid_width;
    endfunction :set_mmussid_width

    function int unsigned get_mmussid_width( );
      get_mmussid_width = m_mmussid_width;
    endfunction :get_mmussid_width

    // max_delay_cycles
    function void set_max_delay_cycles( int unsigned new_max_delay_cycles );
     `uvm_info($sformatf("%0s_CONFIG_MAX_DELAY_cycles", this.name), $sformatf("NEW_CFG_MAX_DELAY_cycles=%0d(d)", new_max_delay_cycles), UVM_DEBUG);
      m_max_delay_cycles = new_max_delay_cycles;
    endfunction :set_max_delay_cycles

    function int unsigned get_max_delay_cycles( );
      get_max_delay_cycles = m_max_delay_cycles;
    endfunction :get_max_delay_cycles

    // max_channel_delay_cycles
    function void set_max_channel_delay_cycles( int unsigned new_max_channel_delay_cycles );
     `uvm_info($sformatf("%0s_CONFIG_MAX_CHANNEL_DELAY_cycles", this.name), $sformatf("NEW_CFG_MAX_CHANNEL_DELAY_cycles=%0d(d)", new_max_channel_delay_cycles), UVM_DEBUG);
      m_max_channel_delay_cycles = new_max_channel_delay_cycles;
    endfunction :set_max_channel_delay_cycles

    function int unsigned get_max_channel_delay_cycles( );
      get_max_channel_delay_cycles = m_max_channel_delay_cycles;
    endfunction :get_max_channel_delay_cycles


    // -----------------------------------------------------------------------
    // Constructor
    // -----------------------------------------------------------------------
    function new( string name = "");
        super.new(name);
        this.name = name;

        // Default value of the configuration
        m_id_width      = MAX_ID_WIDTH      ;
        m_addr_width    = MAX_ADDR_WIDTH    ;
        m_data_width    = MAX_DATA_WIDTH    ;
        m_user_width    = MAX_USER_WIDTH    ;
        m_loop_width    = MAX_LOOP_WIDTH    ;
        m_mmusid_width  = MAX_MMUSID_WIDTH  ;
        m_mmussid_width = MAX_MMUSSID_WIDTH ;

        m_max_delay_cycles = 5 ;
        m_max_channel_delay_cycles = 16 ;

    endfunction

    // ------------------------------------------------------------------------
    // convert2string
    // ------------------------------------------------------------------------
    virtual function string convert2string;
        string s;

        s = super.convert2string();
        s = $sformatf("%0s : ", this.name);
        s = $sformatf("%0s ID_WIDTH=%0d(d),"        , s , m_id_width         ) ;
        s = $sformatf("%0s ADDR_WIDTH=%0d(d),"      , s , m_addr_width       ) ;
        s = $sformatf("%0s DATA_WIDTH=%0d(d),"      , s , m_data_width       ) ;
        s = $sformatf("%0s USER_WIDTH=%0d(d),"      , s , m_user_width       ) ;
        s = $sformatf("%0s LOOP_WIDTH=%0d(d),"      , s , m_loop_width       ) ;
        s = $sformatf("%0s MMUSID_WIDTH=%0d(d),"    , s , m_mmusid_width     ) ;
        s = $sformatf("%0s MMUSSID_WIDTH=%0d(d),"   , s , m_mmussid_width    ) ;
        s = $sformatf("%0s MAX_DELAY_CYCLES=%0d(d),", s , m_max_delay_cycles ) ;

        return s;
    endfunction: convert2string

endclass: uvma_axi_transaction_cfg_c

`endif // __UVMA_AXI_TRANSACTION_CFG_SV__
