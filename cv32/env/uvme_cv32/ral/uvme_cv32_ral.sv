// COPYRIGHT HEADER


`ifndef __UVME_CV32_RAL_SV__
`define __UVME_CV32_RAL_SV__


/**
 * Top-level object encapsulating CV32 Register Abstraction Layer
 * (RAL).
 */
class uvme_cv32_ral_c extends uvm_reg_block;
   
   // Sub-Blocks
   // TODO Add sub-block(s)
   //      Ex: rand uvme_cv32_abc_reg_block_c  abc;
   
   // Registers
   // TODO Add register(s)
   //      Ex: rand uvme_cv32_xyz_reg_c  xyz;
   
   
   `uvm_object_utils_begin(uvme_cv32_ral_c)
      // TODO Add field macros for sub-block(s) and register(s)
      //      Ex: `uvm_field_object(abc, UVM_DEFAULT)
      //          `uvm_field_object(xyz, UVM_DEFAULT)
   `uvm_object_utils_end
   
   
   /**
    * Default constructor.
    */
   extern function new(string name="uvme_cv32_ral");
   
   /**
    * Creates register and register block instances and associates them with this
    * register block.
    */
   extern virtual function void build();
   
endclass : uvme_cv32_ral_c


`pragma protect begin


function uvme_cv32_ral_c::new(string name="uvme_cv32_ral");
   
   super.new(name, UVM_NO_COVERAGE);
   
endfunction : new


function void uvme_cv32_ral_c::build();
   
   // TODO Build sub-block(s)
   //      Ex: abc = uvme_cv32_abc_reg_block_c::type_id::create("abc");
   //          abc.configure(this);
   //          abc.build();
   
   // TODO Build register(s)
   //      Ex:  xyz = uvme_cv32_xyz_reg_c::type_id::create("xyz");
   //           xyz.configure(this);
   //           xyz.build();
   
   // TODO Create default register map (default_map)
   //      Ex: default_map = create_map(
   //             .name     ("default_map"),
   //             .base_addr(32'h00),
   //             .n_bytes  (4),
   //             .endian   (UVM_LITTLE_ENDIAN)
   //          );
   
   // TODO Add register(s) to register map
   //      Ex: default_map.add_reg(
   //             .rg    (xyz),
   //             .offset(32'h00_00_00_00),
   //             .rights("RW")
   //          );
   
   // Lock this register block from further changes
   lock_model();
   
endfunction: build


`pragma protect end


`endif // _UVME_CV32_RAL_SV__
