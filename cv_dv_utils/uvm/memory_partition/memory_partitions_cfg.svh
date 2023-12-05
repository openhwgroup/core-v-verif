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
//  Description : This class holds the configuration of memory regions:
//                Memory is randomly devided into different regions 
//                low: high: and in between regions
//                Use array low_addr[index] and high_addr[index] to get the
//                region for that index. 
//                For index: 0 its from addr 0 to partition size
//                For Index: MAX its from {addr_width{1'b1}} - partition_size to {addr_width{1'b1}}
//                For other index memory is divided in regions and addr are
//                calculated
//                
// ----------------------------------------------------------------------------

class memory_partitions_cfg #(int addr_width=32) extends uvm_component;

   // ------------------------------------------
   // USER provides these informations
   // --> Memory to be divided is between: m_max_mem_size & m_min_mem_size
   // --> The size of the partitions is between: m_max_partition_size & m_min_partition_size
   // -->The maximum number of partitions: m_max_num_partition, minimum is 2 
   // --> m_mem_regions: 
   //    -->MEM_CLOSE_REGIONS:  Regions devided are close to each other 
   //    -->MEM_RANDOM_REGIONS: Whole space of memory is divided randomly          
   //    -->MEM_EXTREME_REGIONS:It provides the lowest an highest region 
   // --------------------------------------------
   rand bit [addr_width-1:0]  m_max_mem_size;
   rand bit [addr_width-1:0]  m_min_mem_size;
   rand bit [addr_width-1:0]  m_max_partition_size;
   rand bit [addr_width-1:0]  m_min_partition_size;
   rand int                   m_max_num_partition;
   rand mem_region_t          m_mem_regions;
   // ------------------------------------------

   local rand bit [addr_width-1:0] m_mem_size;   // mem size between max and 16K(with max 6 partitions of 2k max) 
   local rand int                  m_num_partitions;
   local rand int                  m_partition_size[];
   rand bit [addr_width-1:0]       m_low_addr[];
   rand bit [addr_width-1:0]       m_high_addr[];

   // list of write address 
   protected int req_size_list[bit[addr_width -1:0]];


    `uvm_component_param_utils_begin( memory_partitions_cfg #(addr_width) )
       `uvm_field_enum( mem_region_t, m_mem_regions,   UVM_DEFAULT           )
       `uvm_field_int(  m_max_mem_size,                UVM_DEFAULT | UVM_HEX )
       `uvm_field_int(  m_min_mem_size,                UVM_DEFAULT | UVM_HEX )
       `uvm_field_int(  m_max_partition_size,          UVM_DEFAULT | UVM_HEX )
       `uvm_field_int(  m_max_num_partition,           UVM_DEFAULT           )
       `uvm_field_int(  m_min_partition_size,          UVM_DEFAULT | UVM_HEX )
       `uvm_field_int(  m_mem_size,                      UVM_DEFAULT           )
       `uvm_field_int(  m_num_partitions,                UVM_DEFAULT           )
       `uvm_field_sarray_int( m_partition_size,          UVM_DEFAULT           )
       `uvm_field_sarray_int( m_low_addr,                UVM_DEFAULT | UVM_HEX )
       `uvm_field_sarray_int( m_high_addr,               UVM_DEFAULT | UVM_HEX )
    `uvm_component_utils_end

    // ------------------------------------------------------------------------
    // Constructor
    //
    // ------------------------------------------------------------------------
    function new( string name, uvm_component parent);
      super.new(name,parent);
    endfunction: new

   constraint c_mem_size { if(m_mem_regions == MEM_CLOSE_REGIONS)        m_mem_size == m_min_mem_size;
                           else if(m_mem_regions == MEM_EXTREME_REGIONS) m_mem_size == m_max_mem_size;
                           else                                          m_mem_size inside {[m_min_mem_size: m_max_mem_size]};};  

   constraint c_num_partition_min {m_num_partitions >= 2;};
   constraint c_num_partition_max {m_num_partitions <= m_max_num_partition;};

   constraint c_low_addr_size        {m_low_addr.size()  == m_num_partitions;};
   constraint c_high_addr_size       {m_high_addr.size() == m_num_partitions;};
   constraint c_partition_size_size  {m_partition_size.size() == m_num_partitions;};

   constraint c_min_pt_size {foreach (m_partition_size[i]) m_partition_size[i] >= m_min_partition_size;};   
   constraint c_max_pt_size {foreach (m_partition_size[i]) m_partition_size[i] <= m_max_partition_size;};  


   // Constraint for low high addresses 
   constraint c_addr1  { foreach (m_low_addr[i]) m_high_addr[i] - m_low_addr[i] == m_partition_size[i];}
   constraint c_addr2  { m_high_addr[m_num_partitions -1] - m_low_addr[0] == m_mem_size;}
   constraint c_addr3  { foreach (m_low_addr[i]) m_high_addr[i] > m_low_addr[i];}
   constraint c_addr4  { foreach (m_low_addr[i]) if (i > 0) m_low_addr[i] > m_high_addr[i -1];}

   constraint c_solve_part_size_b_addr {solve m_num_partitions before m_low_addr;
                                        solve m_num_partitions before m_high_addr;
                                        solve m_partition_size before m_low_addr;
                                        solve m_partition_size before m_high_addr;
                                        solve m_max_mem_size before m_low_addr;
                                        solve m_max_mem_size before m_high_addr;
                                        solve m_min_mem_size before m_low_addr;
                                        solve m_min_mem_size before m_high_addr;
                                        solve m_mem_regions before m_mem_size;
                                        solve m_mem_size before m_low_addr;
                                        solve m_mem_size before m_high_addr;
                                        solve m_max_partition_size before m_partition_size;
                                        solve m_min_partition_size before m_partition_size;}

   // Get the number of partitions                                          
   function int get_parition_num();
       get_parition_num = m_num_partitions;
   endfunction

   // Get the random regions                                         
   function int get_mem_region();
       get_mem_region = $urandom_range(0, m_num_partitions -1);
   endfunction

   // Get the random address within a provided region
   function [addr_width-1:0] get_addr_in_mem_region(int region);
       bit [addr_width-1:0] addr;
       if(region > m_num_partitions -1) begin
           `uvm_fatal("RWI_MEM_PARTITIONS", $sformatf("Regions %0d(d) is out of range", region ));
       end
       addr                   = $urandom_range(m_high_addr[region], m_low_addr[region]);

       get_addr_in_mem_region = addr;
   endfunction

   // Get the partition size within a provided region
   function [addr_width-1:0] get_partition_size(int region);
       if(region > m_num_partitions -1) begin
           `uvm_fatal("RWI_MEM_PARTITIONS", $sformatf("Regions %0d(d) is out of range", region ));
       end
       get_partition_size = m_partition_size[region];
   endfunction

   // Get the number of partitions
   function int get_num_mem_partitions();
       get_num_mem_partitions = m_num_partitions;
   endfunction

    // ------------------------------------------------------------------------
    // convert2string
    // ------------------------------------------------------------------------
    virtual function void print_memconfig();
        for(int i = 0; i < m_num_partitions; i++) begin
           `uvm_info("MEMORY PARTITION CONFIG", $sformatf( "partition[%0d] : %0x(x) - %0x(x)", i,  m_low_addr[i], m_high_addr[i]), UVM_LOW);
        end

    endfunction

    // Get the request size
    // The request in the case of DRAM can be max high_addr -random_addr
    // --------------------------------------------------------------------
    function int get_request_size(bit [addr_width -1:0] addr, int partition, bit rd_wr);
      int req_size;
      `uvm_info("DRAM GEN GET REQUEST", $sformatf("Addr %0d Partition %0d", addr, partition), UVM_DEBUG);
       // in the case of write generate random size
       if(rd_wr == 1) begin // write 
         req_size            = $urandom_range((m_high_addr[partition] -addr), 1);
         req_size_list[addr] = req_size;
         get_request_size    = req_size;
       end else begin
         get_request_size    = req_size_list[addr];
       end

    endfunction

    // get read or write
    function bit get_rd_wr(bit [addr_width -1:0] addr);
        if(req_size_list.exists(addr)) begin
            get_rd_wr = 0; // read  
        end else begin
            get_rd_wr = 1; // write
        end
    endfunction
endclass : memory_partitions_cfg 

