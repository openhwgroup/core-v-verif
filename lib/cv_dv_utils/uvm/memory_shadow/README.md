# Introduction 
Parametrized Shadow Memory is an UVM object. It keeps the copy of a memory. 

# Parameters 
Following are the parameters 
```
type addr_t: Addresse type (it can be a bit vector or other object (like a class of row and col)  
int data_w : Data width 
```

# Functions 
Shadow Memroy has three functions:
  * WRITE: write(bit [data_w -1: 0] data, addr_t addr, bit [data_w/8 -1: 0] be, bit error,  mem_path_e path, time timestamp, uvm_object sideband = null (optional) )
```
  data : to be written
  be   : bytes to be written 
  error: 1 -> data containing error bits/bytes   
  path : MEM_HDL_ACCESS: Backdoor write to the RTL memory + Update Shadow Memory
  path : MEM_SHADOW_ACCESS : Writes only in the shadow memory 
  sideband : if the user want to store more information into the memory
             shadow, he can create his class derived from uvm_object, and
             give it to the write function to write the sideband of the
             memory_shadow
```

  * READ: read(time timestamp, addr_t addr, mem_path_e path, output bit [data_w -1: 0] data, output bit [data_w/8 -1: 0] be, bit error);
```
  data : data read from the shadow memory/rtl memory
  be   : bytes read from the shadow memory: IN CASE OF MEM_HDL_ACCESS this field doesnt mean anything
  path : MEM_HDL_ACCESS: Backdoor read from  RTL memory
  path : MEM_SHADOW_ACCESS : Read from  the shadow memory 
  error: 1 -> error was injected 
```
  
  * COMPARE: compare( addr_t addr);
```
  Compare the hdl data with memory shadow
```


# API
API used by user to set the hdl for the backdoor read/write/compare
    
## set hdl root: set root of hdl
```
    function void set_hdl_root(string path)
```

## set hdl path for every addr 
```
    function void set_hdl_path(string path, int which_word);
    function void delete_hdl_path(int which_word);
```

## set hdl size : size of the word read per memory cut
```
    function void set_word_size_per_cut(int which_word, int size);
```
## get hdl root 
```
    function string get_hdl_root();
```
## API used by user to write customized write and read for the backdoor access 
User needs to provide following function to read/write memory by backdoor 
```
    virtual function void write_to_mem(addr_t addr, bit [data_w -1: 0] data, bit [data_w/8 -1: 0]be);
    virtual function void read_from_mem(addr_t addr, output bit [data_w -1: 0] data, bit [data_w/8 -1: 0]be);
```

## API used by user to access the sideband field of the memory_shadow_object 
```
    virtual function void set_sideband_info(addr_t addr, uvm_object sideband);
    virtual function uvm_object get_sideband_info(addr_t addr);
```
# Integration 

Create Shadow Memory (usualy in scoreboard) 

```
    import memory_shadow_pkg::*;
    
    memory_shadow_c #(addr_width, data_width)               mem_shadow;
    mem_shadow           =  memory_shadow_c #(addr_width, data_width)::type_id::create("MEM SHADOW", this); 

```

## Backdoor access APIs example 

Set HDL path for every address 

```
        for(int j = 0; j < 512; j++) begin

           // Set hdl path for the two memory cut
           mem_path = "top/dut/ram_0/j";
           mem_shadow.set_hdl_path(mem_path, 0);
           mem_path = "top/dut/ram_1/j+512";
           mem_shadow.set_hdl_path(mem_path, 1);
        end 
```

Set word size for each cut 
```
        mem_shadow.set_word_size_per_cut(0, 128/8);
        mem_shadow.set_word_size_per_cut(1, 128/8);
```
Set HDL rool 

```
        mem_shadow.set_hdl_root("HDL ROOT");
```

Everytime a write transaction is observed write into the shadow memory 

**mem_shadow.write(...)**

Everytime a read transaction is observed read from the shadow memory and comapre the read data 

**mem_shadow.read(...)**

If backdoor related read/write functions are provided function compare can be used to compare the data in shadow memory and RTL memory

**mem_shadow.compare(...)**

## Licensing
The memory_shadow is released under the Apache License, Version 2.0.
Please refer to the [LICENSE](LICENSE) file for further information.

