/*
 * Copyright 2022 Silicon Laboratories Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//-----------------------------------------------------------------------------------------
//
// CV32E40S random zcmp instruction stream
//
//-----------------------------------------------------------------------------------------
class corev_zcmp_pushpop_base_stream extends riscv_directed_instr_stream;

  `uvm_object_utils(corev_zcmp_pushpop_base_stream)

  rand int num_mixed_instr;

  constraint num_mixed_c {
    num_mixed_instr inside {[1:50]};
  }

  function new(string name = "");
    super.new(name);
  endfunction : new

  extern function void generate_pushpop_instr();
  extern function void generate_pushpopret_instr();
  extern function void generate_pushpopretz_instr();
  extern function void generate_mvsa01_instr();
  extern function void generate_mva01s_instr();
  extern function void post_randomize();
  extern function void add_mixed_instr(int instr_cnt);

endclass : corev_zcmp_pushpop_base_stream

// -----------------------------------------------------------------------------

function void corev_zcmp_pushpop_base_stream::generate_pushpop_instr();
  riscv_compressed_instr instr;
  bit [1:0] saved_spimm;
  bit [3:0] saved_rlist;

  instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_PUSH})));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
    instr_name == CM_PUSH;
    , "Failed randomizing CM.PUSH"
  )

  saved_spimm = instr.spimm;
  saved_rlist = instr.rlist;

  instr.comment = $sformatf("start zcmp push pop instr sequence");
  insert_instr(instr, 0);

  instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_POP})));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
    instr_name == CM_POP;
    spimm      == local::saved_spimm;
    rlist      == local::saved_rlist;
    , "Failed randomizing CM.PUSH"
  )

  instr.comment = $sformatf("end zcmp push pop instr sequence");
  insert_instr(instr, 1);

endfunction : generate_pushpop_instr

// -----------------------------------------------------------------------------

function void corev_zcmp_pushpop_base_stream::generate_pushpopret_instr();
  riscv_compressed_instr instr;
  riscv_pseudo_instr la_instr;

  bit [1:0] saved_spimm;
  bit [3:0] saved_rlist;

  // Backup ra, we might as well use push here
  instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_PUSH})));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
    instr_name == CM_PUSH;
    spimm == 2'h0; // No additional stack adjust
    rlist == 4'h4; // RA only
    , "Failed randomizing CM.PUSH"
  )
  instr.comment = $sformatf("start zcmp push popret instr sequence");
  insert_instr(instr, 0);

  la_instr = riscv_pseudo_instr::type_id::create("la_instr");
  `DV_CHECK_RANDOMIZE_WITH_FATAL(la_instr,
    pseudo_instr_name == LA;
    rd == RA;
    , "Failed randomizing LA"
  )
  la_instr.imm_str = $sformatf("popret_%0d", get_inst_id());
  insert_instr(riscv_instr'(la_instr), 1);

  instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_PUSH})));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
    instr_name == CM_PUSH;
    , "Failed randomizing CM.PUSH"
  )

  saved_spimm = instr.spimm;
  saved_rlist = instr.rlist;

  instr.atomic = 1'b1;
  insert_instr(instr, 2);

  instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_POPRET})));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
    instr_name == CM_POPRET;
    spimm      == local::saved_spimm;
    rlist      == local::saved_rlist;
    , "Failed randomizing CM.PUSH"
  )
  instr.atomic = 1'b0;
  insert_instr(instr, 3);

  // restore ra after return
  instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_POP})));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
    instr_name == CM_POP;
    spimm      == 2'h0;
    rlist      == 4'h4;
    , "Failed randomizing CM.PUSH"
  )

  instr.comment = $sformatf("end zcmp push popret instr sequence");
  insert_instr(instr, 4);

endfunction : generate_pushpopret_instr

// -----------------------------------------------------------------------------

function void corev_zcmp_pushpop_base_stream::generate_pushpopretz_instr();
  riscv_compressed_instr instr;
  riscv_pseudo_instr la_instr;

  bit [1:0] saved_spimm;
  bit [3:0] saved_rlist;

  // Backup ra, we might as well use push here
  instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_PUSH})));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
    instr_name == CM_PUSH;
    spimm == 2'h0; // No additional stack adjust
    rlist == 4'h4; // RA only
    , "Failed randomizing CM.PUSH"
  )
  instr.comment = $sformatf("start zcmp push popretz instr sequence");
  insert_instr(instr, 0);

  la_instr = riscv_pseudo_instr::type_id::create("la_instr");
  `DV_CHECK_RANDOMIZE_WITH_FATAL(la_instr,
    pseudo_instr_name == LA;
    rd == RA;
    , "Failed randomizing LA"
  )
  la_instr.imm_str = $sformatf("popretz_%0d", get_inst_id());
  insert_instr(riscv_instr'(la_instr), 1);

  instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_PUSH})));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
    instr_name == CM_PUSH;
    , "Failed randomizing CM.PUSH"
  )

  saved_spimm = instr.spimm;
  saved_rlist = instr.rlist;

  instr.atomic = 1'b1;
  insert_instr(instr, 2);

  instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_POPRETZ})));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
    instr_name == CM_POPRETZ;
    spimm      == local::saved_spimm;
    rlist      == local::saved_rlist;
    , "Failed randomizing CM.PUSH"
  )
  instr.atomic = 1'b0;
  insert_instr(instr, 3);

  // restore ra after return
  instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_POP})));
  `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
    instr_name == CM_POP;
    spimm      == 2'h0;
    rlist      == 4'h4;
    , "Failed randomizing CM.PUSH"
  )

  instr.comment = $sformatf("end zcmp push popretz instr sequence");
  insert_instr(instr, 4);

endfunction : generate_pushpopretz_instr

// -----------------------------------------------------------------------------

function void corev_zcmp_pushpop_base_stream::generate_mvsa01_instr();
  riscv_compressed_instr instr;
  riscv_reg_t saved_rs1;
  riscv_reg_t saved_rs2;

  if (!(cfg.tp inside {A0, A1})) begin
    instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_MVSA01})));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == CM_MVSA01;
      !(sreg1 inside {cfg.reserved_regs});
      !(sreg2 inside {cfg.reserved_regs});
      , "Failed randomizing CM.MVSA01"
    )
    instr.comment = $sformatf("start zcmp mvsa01/mva01s instr sequence");
    saved_rs1 = instr.sreg1;
    saved_rs2 = instr.sreg2;

    insert_instr(instr, 0);

    instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_MVA01S})));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == CM_MVA01S;
      sreg1 == saved_rs1;
      sreg2 == saved_rs2;
      , "Failed randomizing CM.MVA01S"
    )
    instr.comment = $sformatf("end zcmp mvsa01/mva01s instr sequence");
    insert_instr(instr, 1);
  end else begin
    instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({C_NOP})));
    instr.comment = $sformatf("Registers reserved, skipping mvsa01-mva01s sequence");
    insert_instr(instr, 0);
  end

endfunction : generate_mvsa01_instr

// -----------------------------------------------------------------------------

function void corev_zcmp_pushpop_base_stream::generate_mva01s_instr();
  riscv_compressed_instr instr;
  riscv_reg_t saved_rs1;
  riscv_reg_t saved_rs2;

  if (!(cfg.tp inside {A0, A1})) begin
    instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_MVA01S})));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == CM_MVA01S;
      !(sreg1 inside {cfg.reserved_regs});
      !(sreg2 inside {cfg.reserved_regs});
      , "Failed randomizing CM.MVA01S"
    )
    instr.comment = $sformatf("start zcmp mva01s/mvsa01 instr sequence");
    saved_rs1 = instr.sreg1;
    saved_rs2 = instr.sreg2;

    insert_instr(instr, 0);

    instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({CM_MVSA01})));
    `DV_CHECK_RANDOMIZE_WITH_FATAL(instr,
      instr_name == CM_MVSA01;
      sreg1 == saved_rs1;
      sreg2 == saved_rs2;
      , "Failed randomizing CM.MVSA01"
    )
    instr.comment = $sformatf("end zcmp mva01s/mvsa01 instr sequence");
    insert_instr(instr, 1);
  end else begin
    instr = riscv_compressed_instr'(riscv_instr::get_rand_instr(.include_instr({C_NOP})));
    instr.comment = $sformatf("Registers reserved, skipping mva01s-mvsa01 sequence");
    insert_instr(instr, 0);
  end

endfunction : generate_mva01s_instr

// -----------------------------------------------------------------------------

function void corev_zcmp_pushpop_base_stream::post_randomize();

  randsequence(main)
    main:    pop | popret | popretz | mvsa01 | mva01s;
    pop:     {
      generate_pushpop_instr();
      instr_list[$].has_label = 1'b0;
    };
    popret:  {
      generate_pushpopret_instr();
      instr_list[$].label     = $sformatf("popret_%0d", get_inst_id());
    };
    popretz: {
      generate_pushpopretz_instr();
      instr_list[$].label     = $sformatf("popretz_%0d", get_inst_id());
    };
    mva01s:  {
      generate_mva01s_instr();
      instr_list[$].has_label = 1'b0;
    };
    mvsa01:  {
      generate_mvsa01_instr();
      instr_list[$].has_label = 1'b0;
    };
  endsequence
  add_mixed_instr(num_mixed_instr);

  foreach(instr_list[i]) begin
    if (i < instr_list.size()-1) begin
      instr_list[i].has_label = 1'b0;
    end
    instr_list[i].atomic    = 1'b1;
  end

  instr_list[0].comment   = $sformatf("Start %0s", get_name());
  instr_list[$].comment   = $sformatf("End %0s", get_name());

  if(label != "") begin
    instr_list[0].label = label;
    instr_list[0].has_label = 1'b1;
  end
endfunction : post_randomize

function void corev_zcmp_pushpop_base_stream::add_mixed_instr(int instr_cnt);
  riscv_instr instr;
  setup_allowed_instr(.no_branch(1), .no_load_store(1));
  for (int i = 0; i < instr_cnt; i++) begin
    instr = riscv_instr::type_id::create("instr");
    randomize_instr(instr);
    // Don't want to tamper with RA/SP as that breaks the
    // intended sequence flow as there are dependencies on theses
    // TODO constrain somehow rather than rerandomize
    while (instr.rd == RA || instr.rd == SP || instr.rd == cfg.tp) begin
      randomize_instr(instr);
    end
    insert_instr(instr);
  end
endfunction : add_mixed_instr
