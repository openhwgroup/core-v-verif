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
//  Description : Keep a copy of the memory 
//  It has three functions:
//  WRITE: write(bit [data_w -1: 0] data, addr_t addr, bit [data_w/8 -1: 0] be, bit error,  mem_path_e path, time timestamp, uvm_object sideband = null (optional) )
//  data : to be written
//  be   : bytes to be written 
//  error: 1 -> data containing error bits/bytes   
//  path : MEM_HDL_ACCESS: Backdoor write to the RTL memory + Update Shadow Memory
//  path : MEM_SHADOW_ACCESS : Writes only in the shadow memory 
//  sideband : if the user want to store more information into the memory
//             shadow, he can create his class derived from uvm_object, and
//             give it to the write function to write the sideband of the
//             memory_shadow
//
//  READ: read(time timestamp, addr_t addr, mem_path_e path, output bit [data_w -1: 0] data, output bit [data_w/8 -1: 0] be, bit error);
//  data : data read from the shadow memory/rtl memory
//  be   : bytes read from the shadow memory: IN CASE OF MEM_HDL_ACCESS this field doesnt mean anything
//  path : MEM_HDL_ACCESS: Backdoor read from  RTL memory
//  path : MEM_SHADOW_ACCESS : Read from  the shadow memory 
//  error: 1 -> error was injected 
//  
//  COMPARE: compare( addr_t addr);
//  Compare the hdl data with memory shadow
//
//  ASSUMPTION: It is assumed, for the MEM_HDL_ACCESS that on or multiple ram
//  cut are used to create a sram word
//
//  SET_SIDEBAND_INFO: void set_sideband_info(addr_t addr, uvm_object sideband)
//  addr: address of the memory where you want to write your sideband infos
//  sideband: infos that you want to write
//
//  GET_SIDEBAND_INFO: sideband = get_sideband_info(addr_t addr)
//  addr: address of the memory_shadow sideband that you want to get
//  sideband: copy of the sideband that was read from the memory shadow
//
//
// ----------------------------------------------------------------------------

//----------------------------------------------------------------
// memory shadow
//----------------------------------------------------------------
class memory_shadow_object#(type addr_t = int, int data_w = 32) extends uvm_object; 
    // ------------------------------------------------------------------------
    // UVM Utils for randomized fields
    // ------------------------------------------------------------------------
    `uvm_object_param_utils( memory_shadow_object#(addr_t, data_w) )

    bit [data_w -1:0]     m_data;
    bit [data_w/8 -1:0]   m_be;
    int                   m_req_ts[data_w/8];
    bit [data_w/8 -1:0]   m_error; // error per byte
    
    // Empty object that can be used to store fields that are only used in one
    // project and not in other projects
    uvm_object            m_sideband;

    // ------------------------------------------------------------------------
    // Constructor
    // ------------------------------------------------------------------------
    function new( string name = "memory shadow" );
      super.new(name);
    endfunction: new


endclass: memory_shadow_object
//----------------------------------------------------------------
// memory shadow
//----------------------------------------------------------------
class memory_shadow_c #(type addr_t = int, int data_w = 32) extends uvm_component; 
    // ------------------------------------------------------------------------
    // UVM Utils for randomized fields
    // ------------------------------------------------------------------------
    `uvm_component_param_utils( memory_shadow_c#(addr_t, data_w) )

    typedef  addr_t key_t;
    typedef  memory_shadow_object #(addr_t, data_w) memory_shadow_object_param_t;
    
    protected string    m_hdl_root; // hdl root path to be set by user
    // -------------------------------------------------
    // Actual shadow memory 
    // -------------------------------------------------
    memory_shadow_object_param_t      m_memory_shadow[key_t];

    // -------------------------------------------------
    // Shadow Memor maintains a checksum of read and write data  
    // -------------------------------------------------
    bit [data_w -1 : 0]             m_write_checksum; 
    bit [data_w -1 : 0]             m_read_checksum; 

    // -------------------------------------------------
    // The queue of string containts path of every word for a give address
    // It is assume that the access word size is greater or equal to word size
    // in the memory cut
    // ------------------------------------------------
    string                       m_hdl_path[int];      //addr is the key 
    int                          m_word_size_per_cut[int];   // which_word is the key 

    // -----------------------------------------------------------------------
    // Constructor
    // -----------------------------------------------------------------------
    function new( string name, uvm_component parent);
       super.new(name,parent);
    endfunction: new

    virtual task reset_phase(uvm_phase phase);
       super.reset_phase(phase);

       m_memory_shadow.delete();

    endtask

    // -----------------------------------------
    // Functions to access shadow memo 
    // memory_write:
    // data: data to be written of type addr_t
    // be  : A bit 1'b1 -> corresponding(index of the bit in byte enable) byte to be written 
    // -----------------------------------------
    virtual function void write(bit [data_w -1: 0] data, addr_t addr, bit [data_w/8 -1: 0] be, bit [data_w/8 -1: 0] error, mem_path_e path, time timestamp, uvm_object sideband = null);

	    memory_shadow_object_param_t        new_memory_entry;
        int                               byte_cnt;
        bit [data_w -1: 0]                hdl_data;
         
	    new_memory_entry      =  memory_shadow_object_param_t::type_id::create("memory write entry");

        if(m_memory_shadow.exists(addr)) begin
           new_memory_entry.m_data    = m_memory_shadow[addr].m_data;
           new_memory_entry.m_be      = m_memory_shadow[addr].m_be;
           new_memory_entry.m_error   = m_memory_shadow[addr].m_error;
           // if sideband arg is null, the info stored in sideband field are
           // kept
           if (sideband == null) begin
               new_memory_entry.m_sideband = get_sideband_info(addr);
           end

           `uvm_info("MEMORY SHADOW", $sformatf("Addr already exists:  %s BE=%0x(x) DATA=%0x(x)",  print_addr(addr), new_memory_entry.m_be, new_memory_entry.m_data), UVM_MEDIUM);
           m_memory_shadow.delete(addr);
        end

        foreach(be[i]) begin

           if(be[i] == 1'b1) begin 
              new_memory_entry.m_data[8*i +:8]    =  data[8*i +: 8];
              new_memory_entry.m_be[i]            =  1'b1;
              new_memory_entry.m_req_ts[i]        =  timestamp;
              if(error[i] == 1'b1) begin 
                 new_memory_entry.m_error[i]      =  1'b1;
              end else begin
                 new_memory_entry.m_error[i]      =  1'b0;
              end
           end
     	end //foreach


        // ---------------------------------------------
        // Back door write to the RTL 
        // --------------------------------------------
        if(path == MEM_HDL_ACCESS) begin
            write_to_mem(addr, new_memory_entry.m_data, new_memory_entry.m_be);
        end

	    m_memory_shadow[addr]             =  new_memory_entry;
       
        // Write the new sideband infos into the memory shadow
        if (sideband != null) begin
            set_sideband_info(addr, sideband);
        end

        `uvm_info("MEMORY SHADOW", $sformatf("Data write to memory shadow: %s BE=%0x(x) DATA=%0x(x)  Error=%0x(x) TIME=%0d(d)",  print_addr(addr), new_memory_entry.m_be, new_memory_entry.m_data, new_memory_entry.m_error, timestamp), UVM_HIGH);
        if(path == MEM_SHADOW_ACCESS) begin
           m_write_checksum = m_write_checksum ^ new_memory_entry.m_data;
           `uvm_info("MEMORY SHADOW", $sformatf("%s WRITE CHECKSUM: %0x(x) TIME=%0d(d)", print_addr(addr), m_write_checksum, timestamp), UVM_MEDIUM);
        end
    endfunction

    // -----------------------------------------
    // memory_read: 
    // addr: Addr at which data is written  
    // data: data read
    // be  : byte enable read : A bit 1'b1 -> a byte(at the corresponding
    // index) was written before 
    // -----------------------------------------
    virtual function void read(time timestamp, addr_t addr, mem_path_e path, output bit [data_w -1: 0] data, output bit [data_w/8 -1: 0] be, bit [data_w/8 -1: 0] error);

        bit [data_w -1: 0]         hdl_data;
        bit [data_w -1: 0]         read_data = 0;
        // ---------------------------------------------
        // Back door read from the RTL 
        // --------------------------------------------
        if(path == MEM_HDL_ACCESS) begin
           read_from_mem(addr, data, be);
        end else begin
          // ---------------------------------------------
          // If a write has already happened at this address:
          // return data else return 0 
          // --------------------------------------------
          if(m_memory_shadow.exists(addr)) begin

            for(int i = 0; i < data_w/8; i ++) begin

               if(m_memory_shadow[addr].m_be[i] == 1'b1) begin
                  data[8*i +: 8]  = m_memory_shadow[addr].m_data[8*i +: 8];
                  be[i]           = 1'b1;
                end else begin 
                  data[8*i +: 8]  = 0;
                  be[i]           = 1'b0;
                end //if
                if(m_memory_shadow[addr].m_error[i] == 1'b1) begin
                  error[i]        = 1'b1;
                end else begin 
                  error[i]        = 1'b0;
                end //if
            end //for
          // ------------------------------------------
          // else return 0 with be 0 
          // ------------------------------------------
          end else begin
             data    = 0;
             be      = 1'b0;
             error   = 1'b0;
          end // if
          `uvm_info("memory SHADOW", $sformatf("Data read from memory SHADOW %s BE=%0x(x) ERROR=%0x(x) DATA=%0x(x) TIME=%0d(d)", print_addr(addr), be, error, data, timestamp), UVM_MEDIUM);
        end // if

        if(path == MEM_SHADOW_ACCESS) begin
          m_read_checksum = m_read_checksum ^ data;
          `uvm_info("MEMORY SHADOW", $sformatf("%s READ CHECKSUM %0x(x) TIME=%0d(d)", print_addr(addr), m_read_checksum, timestamp), UVM_MEDIUM);
        end
    endfunction

    // BE belongs to the valid bits in the shadow model
    virtual function int compare( addr_t addr);
        bit [data_w -1: 0] mem_hdl_data;
        bit [data_w -1: 0] mem_shadow_data;
        bit [data_w -1: 0] hdl_data;
        bit [data_w -1: 0] shift_hdl_data;
        bit [data_w/8 -1: 0] be;     
        bit [data_w/8 -1: 0] error; 
        // ---------------------------------------------
        // Back door read from the RTL 
        // --------------------------------------------
        read_from_mem(addr, mem_hdl_data, be);

        // ---------------------------------------------
        // If a write has already happened at this address:
        // return data else return 0 
        // --------------------------------------------
        if(m_memory_shadow.exists(addr)) begin
           mem_shadow_data  = m_memory_shadow[addr].m_data;
           error            = m_memory_shadow[addr].m_error;
        // ------------------------------------------
        // else return 0 with be 0 
        // ------------------------------------------
        end else begin
           mem_shadow_data    = 0;
        end // if

        if(error == 0) begin
          if(mem_shadow_data != mem_hdl_data) begin
             `uvm_error("MEMORY HDL DATA RD MISMATCH", $sformatf("Data read from memory SHADOW %s MEM_SHADOW_DATA=%0x(x) MEM_HDL_DATA=%0x(x)", print_addr(addr), mem_shadow_data, mem_hdl_data));
             return 0;
          end else begin 
             `uvm_info("MEMORY HDL DATA RD MATCH", $sformatf("Data read from memory SHADOW %s MEM_SHADOW_DATA=%0x(x) MEM_HDL_DATA=%0x(x)", print_addr(addr), mem_shadow_data, mem_hdl_data), UVM_MEDIUM);
             return 1;
          end
        end else begin
            `uvm_error("MEMORY HDL DATA RD ERROR BITS", $sformatf("Data read from memory SHADOW %s MEM_SHADOW_DATA=%0x(x) MEM_HDL_DATA=%0x(x)", print_addr(addr), mem_shadow_data, mem_hdl_data));
            return 0;
        end
    endfunction
    // ------------------------------------------------------------------------
    // convert2string
    // ------------------------------------------------------------------------
    virtual function string print_addr(addr_t addr);
        string s;
        s = $sformatf( "ADDR=%0x(x)", addr);

        return s;
    endfunction

    // ---------------------------------------------------------------------
    // API used by user to set the hdl for the backdoor read/write/compare
    // set hdl path for every addr 
    // set hdl size : size of the word read per memory cut
    // EX: RAM WORD SIZE: 256 is made of two memory cut of word size: 128 each
    // ---------------------------------------------------------------------
    function void set_hdl_root(string path);
        m_hdl_root = path;
    endfunction

    function void set_hdl_path(string path, int which_word);
        m_hdl_path[which_word] = path;
    endfunction

    function void delete_hdl_path(int which_word);
        m_hdl_path.delete(which_word);
    endfunction

    function void set_word_size_per_cut(int which_word, int size);
        m_word_size_per_cut[which_word] = size;
    endfunction

    function string get_hdl_root();
        get_hdl_root = m_hdl_root;
    endfunction
    // ---------------------------------------------------------------------
    // API used by user to write customized write and read for the backdoor
    // access  
    // ---------------------------------------------------------------------
    virtual function void write_to_mem(addr_t addr, bit [data_w -1: 0] data, bit [data_w/8 -1: 0]be);
    endfunction

    virtual function void read_from_mem(addr_t addr, output bit [data_w -1: 0] data, bit [data_w/8 -1: 0]be);
    endfunction

    // ---------------------------------------------------------------------
    // API used by user to access the sideband field of the
    // memory_shadow_object 
    // ---------------------------------------------------------------------
    virtual function void set_sideband_info(addr_t addr, uvm_object sideband);
        m_memory_shadow[addr].m_sideband = sideband;
    endfunction : set_sideband_info

    virtual function uvm_object get_sideband_info(addr_t addr);
        return m_memory_shadow[addr].m_sideband;
    endfunction : get_sideband_info

endclass: memory_shadow_c
