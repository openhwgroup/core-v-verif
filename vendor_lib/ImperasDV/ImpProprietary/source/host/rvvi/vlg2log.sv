/*
 *
 * Copyright (c) 2005-2022 Imperas Software Ltd., All Rights Reserved.
 *
 * THIS SOFTWARE CONTAINS CONFIDENTIAL INFORMATION AND TRADE SECRETS
 * OF IMPERAS SOFTWARE LTD. USE, DISCLOSURE, OR REPRODUCTION IS PROHIBITED
 * EXCEPT AS MAY BE PROVIDED FOR IN A WRITTEN AGREEMENT WITH
 * IMPERAS SOFTWARE LTD.
 *
 */

`include "rvvi/rvvi-api.svh"

`define NUM_REGS 32
`define NUM_CSRS 4096

module VLG2LOG
#(
    parameter int ILEN    = 32,
    parameter int XLEN    = 32,
    parameter int FLEN    = 32,
    parameter int VLEN    = 256,
    parameter int NHART   = 1,
    parameter int ISSUE   = 1
)
(RVVI_VLG rvvi);
import rvvi_pkg::*;

    bit valid;
    bit trap;

    bit state;
    bit net;
    string disass;

    longint order;
    longint reorder_min, reorder_max;

    int    hart, issue;
    string info_str;
    int    value;

    function automatic void GPR_get(int hart, int issue);
        bit [(`NUM_REGS-1):0] mask, wb;
        int idx; int popcnt=0;
        
        wb = rvvi.x_wb[hart][issue];
        if (wb != 'b0) begin
            for(idx=1; idx<`NUM_REGS; idx++) begin
                mask = 1<<idx;
                if ((mask & wb) != 'b0) begin
                    if (popcnt>0) begin
                        info_str = {info_str, " "};
                    end
                    info_str = {info_str, $sformatf("x%0d=%X", idx, rvvi.x_wdata[hart][issue][idx])};
                    popcnt++;
                end
            end
        end
        info_str = {info_str, ","};
    endfunction

    function automatic void FPR_get(int hart, int issue);
        bit [(`NUM_REGS-1):0] mask, wb;
        int idx; int popcnt=0;

        wb = rvvi.f_wb[hart][issue];
        if (wb != 'b0) begin
            for(idx=0; idx<`NUM_REGS; idx++) begin
                mask = 1<<idx;
                if ((mask & wb) != 'b0) begin
                    if (popcnt>0) begin
                        info_str = {info_str, " "};
                    end
                    info_str = {info_str, $sformatf("f%0d=%X", idx, rvvi.f_wdata[hart][issue][idx])};
                    popcnt++;
                end
            end
        end
        info_str = {info_str, ","};
    endfunction

    function automatic void VR_get(int hart, int issue);
        bit [(`NUM_REGS-1):0] mask, wb;
        int idx; int popcnt=0;

        wb = rvvi.f_wb[hart][issue];
        if (wb != 'b0) begin
            for(idx=0; idx<`NUM_REGS; idx++) begin
                mask = 1<<idx;
                if ((mask & wb) != 'b0) begin
                    if (popcnt>0) begin
                        info_str = {info_str, " "};
                    end
                    info_str = {info_str, $sformatf("v%0d=%X", idx, rvvi.v_wdata[hart][issue][idx])};
                    popcnt++;
                end
            end
        end
        info_str = {info_str, ","};
    endfunction

    bit init = 0;
    shortint present[`NUM_CSRS]; // index or -1
    shortint midx;
    
    function automatic void CSR_get(int hart, int issue);
        bit [(`NUM_CSRS-1):0] mask, wb;
        shortint idx; 
        int popcnt=0;

        // one-time only initialize the registers present
        if (!init) begin
            bit isPresent;
            init = 1;
            midx = 0;
            for(idx=0; idx<`NUM_CSRS; idx++) begin
                isPresent = bit'(rvviRefCsrPresent(hart, int'(idx)));
                present[12'(idx)] = -1;
                if (isPresent) begin
                    present[12'(midx)] = 16'(idx);
                    midx++;
                end
            end
        end
        
        wb = rvvi.csr_wb[hart][issue];
        if (wb != 'b0) begin
            for(idx=0; idx<midx; idx++) begin
                shortint csr;
                string   name;
                
                csr = present[12'(idx)];
                mask = 1<<csr;
                if ((mask & wb) != 'b0) begin
                    if (popcnt>0) begin
                        info_str = {info_str, " "};
                    end
                    name = rvviRefCsrName(hart, 32'(csr));
                    info_str = {info_str, $sformatf("CSR%03x(%0s)=%X", csr, name, rvvi.csr[hart][issue][csr])};
                    popcnt++;
                end
            end
        end
        info_str = {info_str, ","};
    endfunction

    function automatic void DIS_get(int hart, int issue);
        disass = rvviDasmInsBin(hart, 64'(rvvi.insn[hart][issue]));
        info_str = {info_str, $sformatf("\"%-32s\"", disass)};
        info_str = {info_str, ","};
    endfunction

    always @(posedge rvvi.clkD) begin
        reorder_min = 0;
        reorder_max = 0;
        state       = 0;

        //
        // calculate the min/max retirement ordering bounds
        // this allows us to reorder into program order
        //
        for(hart=0; hart<rvvi.NHART; hart++) begin
            for(issue=0; issue<rvvi.ISSUE; issue++) begin
                valid = rvvi.valid[hart][issue];
                order = rvvi.order[hart][issue];
                trap  = rvvi.trap[hart][issue];
                if (valid) begin
                    state |= 1;
                    if (reorder_min==0 || (rvvi.order[hart][issue] < reorder_min))
                        reorder_min = order;

                    if (reorder_max==0 || (rvvi.order[hart][issue] > reorder_max))
                        reorder_max = order;
                end
            end
        end

        //
        // process RVVI events in program order
        //
        while (ENABLE && state && (reorder_min <= reorder_max)) begin
            for(hart=0; hart<rvvi.NHART; hart++) begin
                for(issue=0; issue<rvvi.ISSUE; issue++) begin
                    valid = rvvi.valid[hart][issue];
                    if (!valid) continue;

                    order = rvvi.order[hart][issue];
                    trap  = rvvi.trap[hart][issue];

                    info_str = $sformatf("%m @ %0t: ", $time);
                    if (order==reorder_min) begin
                        if (trap) begin
                            info_str = {info_str, $sformatf("EXC,%0d,%0d,%08X,", hart, order, rvvi.pc_rdata[hart][issue])};
                        end else begin
                            info_str = {info_str, $sformatf("RET,%0d,%0d,%08X,", hart, order, rvvi.pc_rdata[hart][issue])};
                        end

                        // Print Register Changes
                        DIS_get(hart, issue);
                        GPR_get(hart, issue);
                        FPR_get(hart, issue);
                        VR_get(hart, issue);
                        CSR_get(hart, issue);
                        info_str = {info_str, "\n"};
                        msgnote(info_str);
                        info_str = ""; // "flush" after writing to stdout

                        reorder_min++;
                    end
                end
            end
        end

    end // always

endmodule: VLG2LOG
