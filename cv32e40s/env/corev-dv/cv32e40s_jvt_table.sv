virtual class corev_zcmt_jvt_table;
  rand riscv_reg_t jvt_addr;
  rand bit [7:0]   jvt_size;
  riscv_instr      jvt_contents[$];

  function new();
    // Create empty table of correct size
    for (int i = 0; i < jvt_size; i++) begin
      jvt_contents.push_back('0);
    end
  endfunction : new

endclass : corev_zcmt_jvt_table
