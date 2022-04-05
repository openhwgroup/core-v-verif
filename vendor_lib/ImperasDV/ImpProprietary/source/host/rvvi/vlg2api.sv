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

module VLG2API import rvvi_pkg::*;
#(
    parameter int ILEN    = 32,
    parameter int XLEN    = 32,
    parameter int FLEN    = 32,
    parameter int VLEN    = 256,
    parameter int NHART   = 1,
    parameter int ISSUE   = 1,
    parameter bit CMP_PC  = 0,
    parameter bit CMP_INS = 0,
    parameter bit CMP_GPR = 0,
    parameter bit CMP_FPR = 0,
    parameter bit CMP_VR  = 0,
    parameter bit CMP_CSR = 0,
    parameter int MISCOMPARES = 1
)
(RVVI_VLG rvvi);

    bit valid;
    bit trap;

    bit state;
    bit net;

    longint order;
    longint reorder_min, reorder_max;

    int    hart, issue;
    string name;
    int    value;
    static int num_miscompares = 0;

    function automatic void GPR_set(int hart, int issue);
        bit [(`NUM_REGS-1):0] mask, wb;
        int idx;
        
        wb = rvvi.x_wb[hart][issue];
        if (wb != 'b0) begin
            for(idx=0; idx<`NUM_REGS; idx++) begin
                mask = 1<<idx;
                if ((mask & wb) != 'b0) begin
                    rvviDutGprSet(hart, idx, 64'(rvvi.x_wdata[hart][issue][idx]));
                end
            end
        end
    endfunction

    function automatic void FPR_set(int hart, int issue);
        bit [(`NUM_REGS-1):0] mask, wb;
        int idx;
        
        wb = rvvi.f_wb[hart][issue];
        if (wb != 'b0) begin
            for(idx=0; idx<`NUM_REGS; idx++) begin
                mask = 1<<idx;
                if ((mask & wb) != 'b0) begin
                    rvviDutFprSet(hart, idx, 64'(rvvi.f_wdata[hart][issue][idx]));
                end
            end
        end
    endfunction

    function automatic void VR_set(int hart, int issue);
        bit [(`NUM_REGS-1):0] mask, wb;
        int idx;
        
        wb = rvvi.v_wb[hart][issue];
        if (wb != 'b0) begin
            for(idx=0; idx<`NUM_REGS; idx++) begin
                mask = 1<<idx;
                if ((mask & wb) != 'b0) begin
                    // rvviDutVrSet(hart, idx, 64'(rvvi.v_wdata[hart][issue][idx]));
                end
            end
        end
    endfunction

    bit init = 0;
    shortint present[`NUM_CSRS]; // index or -1
    shortint midx;
    
    function automatic void CSR_set(int hart, int issue);        
        bit [(`NUM_CSRS-1):0] mask, wb;
        shortint idx;
        
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
            
                csr = present[12'(idx)];
                mask = 1<<csr;
                if ((mask & wb) != 'b0) begin
                    rvviDutCsrSet(hart, 32'(csr), 64'(rvvi.csr[hart][issue][csr]));
                end
            end
        end
    endfunction

    function automatic void STATE_compare(int hart);
        int result;
        result = rvviRefEventStep(hart);
        if (CMP_PC)  result &= rvviRefPcCompare(hart);
        if (CMP_INS) result &= rvviRefInsBinCompare(hart);
        if (CMP_GPR) result &= rvviRefGprsCompare(hart);
        if (CMP_FPR) result &= rvviRefFprsCompare(hart);
        if (CMP_CSR) result &= rvviRefCsrsCompare(hart);
        if (result==0) begin
            msgerror($sformatf("%m @ %0t: MISMATCH", $time));
        end
    endfunction
    
    function automatic void NET_set();
        int     status;
        longint found;
        string  name;
        int     value;

        status = 1;
        while (status==1) begin
            status = rvvi.net_pop(name, value);

            if (status==1) begin
                found = rvviRefNetIndexGet(name);
                if (found == `RVVI_INVALID_INDEX) begin
                    msgfatal($sformatf("%m @ %0t: Error cannot find net %0s", $time, name));
                end else begin
                    msgdebug($sformatf("%m @ %0t: PIN %0s = %0d", $time, name, value));
                    rvviRefNetSet(found, 64'(value));
                end
            end
        end
    endfunction
    
    always @(posedge rvvi.clkD) begin
        reorder_min = 0;
        reorder_max = 0;
        state       = 0;

        //
        // push the nets into the reference
        //
        NET_set();
        
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
        while (state && (reorder_min <= reorder_max)) begin
            for(hart=0; hart<rvvi.NHART; hart++) begin
                for(issue=0; issue<rvvi.ISSUE; issue++) begin
                    valid = rvvi.valid[hart][issue];
                    if (!valid) continue;

                    order = rvvi.order[hart][issue];
                    trap  = rvvi.trap[hart][issue];

                    if (order==reorder_min) begin
                        msgdebug($sformatf("%m @ %0t: ACTIVE hart%0d issue%0d trap=%0d PC=%08X order=%0d",
                                                      $time, hart, issue, trap, rvvi.pc_rdata[hart][issue], order));
                        // Pass Registers to RVVI API
                        GPR_set(hart, issue);
                        FPR_set(hart, issue);
                        VR_set(hart, issue);
                        CSR_set(hart, issue);

                        if (trap) begin
                            rvviDutTrap(hart, 64'(rvvi.pc_rdata[hart][issue]), 64'(rvvi.insn[hart][issue]));
                        end else begin
                            rvviDutRetire(hart, 64'(rvvi.pc_rdata[hart][issue]), 64'(rvvi.insn[hart][issue]));
                        end

                        // Compare the state between DUT and REF
                        STATE_compare(hart);

                        reorder_min++;
                    end
                end
            end
        end
    end

endmodule
