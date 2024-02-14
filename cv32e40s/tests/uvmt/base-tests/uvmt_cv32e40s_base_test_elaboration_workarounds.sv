//
// Copyright 2023 OpenHW Group
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//

`ifndef __UVMT_CV32E40S_BASE_TEST_ELABORATION_WORKAROUNDS_SV__
`define __UVMT_CV32E40S_BASE_TEST_ELABORATION_WORKAROUNDS_SV__


// This file is "`included" into the base-test end_of_elaboration function.
// This is a good place to add in hacks and workarounds during development.
// It should be empty by the end of the project.

////////////////////////////////////////////////////////////////////////////////
// Example things that you might find useful to be running immediately following elaboration:
//
// uvm_root::get().print_topology();
// uvm_root::get().set_report_verbosity_level_hier(UVM_HIGH);

////////////////////////////////////////////////////////////////////////////////
// Depreciate select errors to warnings.
//
// function void set_report_severity_id_override(uvm_severity cur_severity, string id, uvm_severity new_severity);
// Note that "id" is the first argument in `uvm_error(), `uvm_warning(), etc.

// A bunch of assertions in cv32e40s/tb/uvmt/uvmt_cv32e40s_triggers_assert_cov.sv
// are firing with Questasim (do they fire with other simulators?).
`ifdef QUESTA_VSIM
uvm_root::get().set_report_severity_id_override(UVM_ERROR,"TRIGGER_ASSERT",UVM_WARNING);
`endif // QUESTA_VSIM


`endif // __UVMT_CV32E40S_BASE_TEST_ELABORATION_WORKAROUNDS_SV__
