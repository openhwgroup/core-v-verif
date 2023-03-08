typedef class cv32e40p_instr;

`define CV32E40P_INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM) \
    static bit valid = riscv_instr::register(instr_n);  \
    `uvm_object_utils(riscv_``instr_n``_instr)  \
    // int category_i = int'(``instr_category); \
    function new(string name = "");  \
      super.new(name);  \
      this.instr_name = ``instr_n; \
      this.format = ``instr_format; \
      this.group = ``instr_group;  \
      this.category = ``instr_category;  \
      this.imm_type = ``imm_tp;  \
      set_imm_len(); \
      set_rand_mode(); \
    endfunction \
  endclass

// Custom extension instruction
`define DEFINE_CV32E40P_INSTR(instr_n, instr_format, instr_category, instr_group, imm_tp = IMM)  \
  class riscv_``instr_n``_instr extends cv32e40p_instr;  \
    `CV32E40P_INSTR_BODY(instr_n, instr_format, instr_category, instr_group, imm_tp)
