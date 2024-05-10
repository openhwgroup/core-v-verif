// Copyright 2022 Thales DIS SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group


`ifndef __UVMA_AXI_SEQ_ITEM_LOGGER_SV__
`define __UVMA_AXI_SEQ_ITEM_LOGGER_SV__


/**
 * Component writing AXI sequence items debug data to disk as plain text.
 */
class uvma_axi_seq_item_logger_c extends uvml_logs_seq_item_logger_c #(
   .T_TRN  (uvma_axi_transaction_c),
   .T_CFG  (uvma_axi_cfg_c        ),
   .T_CNTXT(uvma_axi_cntxt_c      )
);

   `uvm_component_utils(uvma_axi_seq_item_logger_c)


   /**
    * Default constructor.
    */
   function new(string name="uvma_axi_seq_item_logger", uvm_component parent=null);
      super.new(name, parent);
   endfunction : new

   /**
    * Writes contents of t to disk.
    */
   virtual function void write(uvma_axi_transaction_c t);
      if(cntxt.reset_state == UVMA_AXI_RESET_STATE_POST_RESET)begin

         string aw_access_type  = "";
         string aw_id_str     = "";

         string aw_address   = "";
         string write_addr_starting_time = "";

         string write_data_starting_time = "";
         string w_data    = "";
         string w_access_complet = "";

         string write_response_starting_time = "";
         string b_err    = "";

         string ar_access_type  = "";
         string ar_id_str     = "";

         string ar_address   = "";
         string read_addr_starting_time = "";

         string read_data_starting_time = "";
         string r_data    = "";
         string r_access_complet = "";
         string r_err    = "";

         if(t.access_type == UVMA_AXI_ACCESS_WRITE) begin

            aw_id_str = $sformatf("%b", t.aw_id);
            if(t.aw_lock) begin
               aw_access_type = "Exclusive_access";
            end else begin
               aw_access_type = "Normal_access";
            end

            write_addr_starting_time = $sformatf("%d", t.aw_start_time);
            aw_address = $sformatf("%h", t.aw_addr);

            fwrite($sformatf("----------------------/ WRITE ACCESS | ID : %s | ACCESS TYPE : %s \----------------------", aw_id_str, aw_access_type));

            fwrite($sformatf("----> WRITE ADDRESS START AT TIME %s | ADDRESS : %s", write_addr_starting_time, aw_address));

            foreach(t.w_data_trs[i]) begin

               write_data_starting_time = $sformatf("%d", t.w_data_trs[i].w_start_time);
               w_data = $sformatf("%h", t.w_data_trs[i].w_data);
               if(t.w_data_trs[i].w_last) begin
                  w_access_complet = "Yes";
               end else begin
                  w_access_complet = "No";
               end
               fwrite($sformatf("----> WRITE DATA START AT TIME %s | DATA : %s | LAST DATA : %s ", write_addr_starting_time, w_data, w_access_complet));

            end

            write_response_starting_time = $sformatf("%d", t.b_start_time);
            case (t.b_resp)
               00 : begin
                  if(aw_access_type == "Exclusive_access") b_err = "Err";
                  else b_err = "No Err";
               end
               01 : b_err  = "Err";
               10 : b_err  = "Err";
               11 : begin
                  if(aw_access_type == "Exclusive_access") b_err = "NO Err";
                  else b_err = "Err";
               end
               default : b_err = " ? ";
            endcase

            fwrite($sformatf("----> WRITE RESPONSE START AT TIME %s | RESP : %s ", write_response_starting_time, b_err));

         end else begin

            aw_access_type  = "";
            aw_id_str     = "";

            write_addr_starting_time = "";
            aw_address   = "";

            write_data_starting_time = "";
            w_data  = "";
            w_access_complet   = "";

            write_response_starting_time = "";
            b_err  = "";

         end

         if(t.access_type == UVMA_AXI_ACCESS_READ) begin

            ar_id_str = $sformatf("%b", t.ar_id);
            if(t.ar_lock) begin
               ar_access_type = "Exclusive_access";
            end else begin
               ar_access_type = "Normal_access";
            end

            read_addr_starting_time = $sformatf("%d", t.ar_start_time);
            ar_address = $sformatf("%h", t.ar_addr);

            fwrite($sformatf("----------------------/ READ ACCESS | ID : %s | ACCESS TYPE : %s \----------------------", ar_id_str, ar_access_type));

            fwrite($sformatf("----> READ ADDRESS START AT TIME %s | ADDRESS : %s", read_addr_starting_time, ar_address));

            foreach(t.r_data_trs[i]) begin

               read_data_starting_time = $sformatf("%d", t.r_data_trs[i].r_start_time);
               r_data = $sformatf("%h", t.r_data_trs[i].r_data);
               case (t.r_data_trs[i].r_resp)
                  00 : begin
                     if(aw_access_type == "Exclusive_access") r_err = "Err";
                     else r_err = "No Err";
                  end
                  01 : r_err  = "Err";
                  10 : r_err  = "Err";
                  11 : begin
                     if(aw_access_type == "Exclusive_access") r_err = "NO Err";
                     else r_err = "Err";
                  end
                  default : r_err = " ? ";
               endcase

               if(t.r_data_trs[i].r_last) begin
                  r_access_complet = "Yes";
               end else begin
                  r_access_complet = "No";
               end
               fwrite($sformatf("----> READ DATA START AT TIME %s | DATA : %s | RESP : %s | LAST DATA : %s ", read_data_starting_time, r_data, r_err, r_access_complet));

            end

         end else begin

            ar_access_type  = "";
            ar_id_str     = "";

            read_addr_starting_time = "";
            ar_address   = "";

            read_data_starting_time = "";
            r_data  = "";
            b_err  = "";
            r_access_complet   = "";

         end
      end
   endfunction : write

// A significant chunk of the write_mstr method is common between this
// sequence item logger and the monitor transaction logger.  Given that
// much of this code is template generated, and is not expected to be edited
// further, the duplicated code has a lint waiver.
//
//@DVT_LINTER_WAIVER_START "MT20210901_2" disable SVTB.33.1.0, SVTB.33.2.0
   /**
    * Writes contents of mstr t to disk.
    */

   /**
    * Writes log header to disk.
    */
    virtual function void print_header();

      fwrite("----------------------------------------------------------------------------------------------------------------");
      fwrite("                                         AXI   TRANSACTION LOGGER                                               ");
      fwrite("          (EACH TRANSACTIOBN WILL BE DEFINED SEPARETLY BE SPECIFYING THE START TIME OF EACH TRANSFER)           ");
      fwrite("----------------------------------------------------------------------------------------------------------------");

   endfunction : print_header

endclass : uvma_axi_seq_item_logger_c

/**
 * Component writing Open Bus Interface monitor transactions debug data to disk as JavaScript Object Notation (JSON).
 */
class uvma_axi_seq_item_logger_json_c extends uvma_axi_seq_item_logger_c;

   `uvm_component_utils(uvma_axi_seq_item_logger_json_c)

   /**
    * Set file extension to '.json'.
    */
   function new(string name="uvma_axi_seq_item_logger_json", uvm_component parent=null);

      super.new(name, parent);
      fextension = "json";

   endfunction : new

   /**
    * Writes contents of t to disk.
    */
   virtual function void write(uvma_axi_transaction_c t);


   endfunction : write

   /**
    * Empty function.
    */
   virtual function void print_header();

      // Do nothing: JSON files do not use headers.

   endfunction : print_header

endclass : uvma_axi_seq_item_logger_json_c


`endif // __UVMA_AXI_SEQ_ITEM_LOGGER_SV__
