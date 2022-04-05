/*
 * Copyright (c) 2005-2022 Imperas Software Ltd., www.imperas.com
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
 * either express or implied.
 *
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */
 
`ifndef _RVVI_PKG__
`define _RVVI_PKG__

//
// Format message for UVM/SV environment
// TODO: ID for the UVM macros
//
package rvvi_pkg;
`ifdef UVM
  import uvm_pkg::*;
`endif

  int err_cnt     = 0;
  int warn_cnt    = 0;
  int cmpd_insn   = 0;
  int tb_cycles   = 0;
  int MAX_ERRS    = 0;
  bit VERBOSE     = 0;
  bit ENABLE      = 0;
  bit FATAL       = 1;
  bit debug_level = 0;

  // Always write notes to stdout
  function automatic void msgnote (input string msg);
    `ifdef UVM
      `uvm_info("", msg, UVM_NONE);
    `else
      $display("[NOTE] %s", msg);
    `endif
  endfunction: msgnote

  // Write debug messages if debug_level > 0
  function automatic void msgdebug (input string msg);
    `ifdef UVM
      `uvm_info("", msg, UVM_DEBUG);
    `else
      if (debug_level) $display("[DEBUG] %s", msg);
    `endif
  endfunction: msgdebug

  // Write verbose messages if verbose > 0
  function automatic void msgverbose (input string msg);
    `ifdef UVM
      `uvm_info("", msg, UVM_NONE);
    `else
      if (VERBOSE) $display("[VERBOSE] %s", msg);
    `endif
  endfunction: msgverbose

  // Always write warning and increment warning count
  function automatic void msgwarn (input string msg);
    `ifdef UVM
      `uvm_warn("", msg);
    `else
      $display("[WARNING] %s", msg);
      ++warn_cnt;
    `endif
  endfunction: msgwarn

  // Always write errors and increment error count
  function automatic void msgerror (input string msg);
    `ifdef UVM
      `uvm_error("", msg);
    `else
      $display("[ERROR] %s", msg);
      ++err_cnt;
      if (err_cnt >= MAX_ERRS) begin
        msgfatal($sformatf("\n\n!!!\n!!! %m @ t=%0t: FATAL: too many errors!\n!!!", $time));
      end
    `endif
  endfunction: msgerror

  function automatic void msgfatal(input string reason = "");
    automatic string freason;
    if (reason == "") begin
      freason = "No reason given";
    end
    else begin
      freason = reason;
    end

    terminate_sim(freason, FATAL);
  endfunction

  function automatic void terminate_sim(input string reason = "", input bit fatal = 0);
    automatic string tmsg, treason;

    if (reason == "") begin
      treason = "No reason given";
    end
    else begin
      treason = reason;
    end

    //if (cmpd_insn == 0) begin
    //  msgerror($sformatf("%m @ %0t: No instructions compared!", $time));
    //end

    tmsg = $sformatf("%m @ %0t:\n", $time);
    tmsg = {tmsg, $sformatf("       %0s: %s\n", (fatal ? "FATAL" : "Normal termination"), treason)};
    tmsg = {tmsg, $sformatf("       Ran for %0d clock cycles\n", tb_cycles)};
    tmsg = {tmsg, $sformatf("       Compared %0d instructions\n", cmpd_insn)};
    tmsg = {tmsg, $sformatf("       Test %s", ((err_cnt > 0) || fatal) ? "FAILED" : "PASSED")};
    if (fatal) begin
      tmsg = {tmsg, $sformatf(" due to fatal error(s) and %0d non-fatal errors and %0d warnings.\n\n", err_cnt, warn_cnt)};
    end
    else begin
      tmsg = {tmsg, $sformatf(" with %0d errors and %0d warnings.\n\n", err_cnt, warn_cnt)};
    end
    msgnote(tmsg);
    $finish; // this should be the only call to $finish in the testbench
  endfunction

endpackage: rvvi_pkg

`endif // _RVVI_PKG__
