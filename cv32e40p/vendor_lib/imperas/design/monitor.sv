/*
 *
 * Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com
 *
 * The contents of this file are provided under the Software License
 * Agreement that you accepted before downloading this file.
 *
 * This source forms part of the Software and can be used for educational,
 * training, and demonstration purposes but cannot be used for derivative
 * works except in cases where the derivative works require OVP technology
 * to run.
 *
 * For open source models released under licenses that you can use for
 * derivative works, please visit www.OVPworld.org or www.imperas.com
 * for the location of the open source models.
 *
 */
 
 `include "typedefs.sv"

module MONITOR 
(
    BUS SysBus
);
    int     fd_sym;
    string  fn_sym;
    string  type_sym[string];
    int     addr_sym[string];

    watchT begin_signature;
    watchT end_signature;
    watchT _test_stdout;
    watchT _test_exit;
    watchT _test_intc_machine_external;
    watchT _test_intc_machine_software;  
    watchT _test_intc_machine_timer;  
    watchT trap_vector;
    
    int fd_signature, fd_stdout;
    
    function automatic void split_string (
        output string out [$],
        input string in,
        input string separator = ",",
        input bit drop_blank = 1
    );
        string val;
        bit flag;
        in = {in,separator};
        out.delete();
        foreach (in[i]) begin
            if (drop_blank && in[i] == " ") continue;
            if (in[i] == separator[0]) begin
                if (flag) begin
                    flag = 0;
                end else if (val != "") begin
                    out.push_back(val);
                end
                val = "";
            end else begin
                val = {val, in[i]};
            end
        end
    endfunction
    
    function automatic void nm_get(string name_sym, ref watchT watch);
        if (addr_sym.exists(name_sym)) begin
            watch.addr   = addr_sym[name_sym];
            watch.enable = 1;
        end
    endfunction
    
    function automatic void nm_load();
        int i, j;
        string line;
        string linesplit[$];
        string name_sym;
        
        // simply return if not provided
        if (!($value$plusargs("nm_file=%s", fn_sym))) begin
            return;
        end

        fd_sym = $fopen(fn_sym, "r");
        // simply return if not provided
        if (fd_sym == 0) begin
            return;
        end
        
        while ($fgets(line, fd_sym)) begin
            j = line.len() - 2;
            line = line.substr(0, j);
            
            split_string(linesplit, line, " ", 0);
            name_sym = linesplit[2];
            
            addr_sym[name_sym] = linesplit[0].atohex();
            type_sym[name_sym] = linesplit[1];
        end
        $fclose(fd_sym);
    endfunction
    
    // Generate a signature dump file
    function automatic void dumpSignature();
        automatic int addr = begin_signature.addr;
        automatic string sig_file = "signature.txt";
        
        if (!begin_signature.enable) return;

        if ($value$plusargs("sig_file=%s", sig_file)) ;
        $display("Writing signature %s", sig_file);
        
        $display("Dump Signature 0x%x -> 0x%x", begin_signature.addr, end_signature.addr);

        fd_signature = $fopen(sig_file, "w");

        while (addr < end_signature.addr) begin
            $fwrite(fd_signature, "%x\n", ram.mem[addr>>2]);
            addr = addr + 4;
        end
  
        $fclose(fd_signature);
    endfunction
    
    function void openStdout();
        automatic string stdout_file = "stdout.txt";
        if ($value$plusargs("stdout_file=%s", stdout_file)) ;
        $display("Opening stdout %s", stdout_file);
    
        fd_stdout = $fopen(stdout_file, "w");
    endfunction
    
    function void closeStdout();
        $fclose(fd_stdout);
    endfunction
    
    initial begin
        nm_load();
        
        nm_get("trap_vector"    , trap_vector);
        nm_get("begin_signature", begin_signature);
        nm_get("end_signature"  , end_signature);
        nm_get("_test_stdout"   , _test_stdout);
        
        nm_get("_test_intc_machine_external"  , _test_intc_machine_external);
        nm_get("_test_intc_machine_software"  , _test_intc_machine_software);
        nm_get("_test_intc_machine_timer"     , _test_intc_machine_timer);
        
        nm_get("_test_exit"     , _test_exit);
        nm_get("write_tohost"   , _test_exit); // used for riscv-dv and riscv-compliance

        if (trap_vector.enable)
            $display("trap_vector=%x", trap_vector.addr);
            
        if (begin_signature.enable)
            $display("begin_signature=%x", begin_signature.addr);
        if (end_signature.enable)
            $display("end_signature=%x", end_signature.addr);
            
        if (_test_stdout.enable)
            $display("_test_stdout=%x", _test_stdout.addr);
            
        if (_test_intc_machine_external.enable)
            $display("_test_intc_machine_external=%x", _test_intc_machine_external.addr);
        if (_test_intc_machine_software.enable)
            $display("_test_intc_machine_software=%x", _test_intc_machine_software.addr);
        if (_test_intc_machine_timer.enable)
            $display("_test_intc_machine_timer=%x", _test_intc_machine_timer.addr);
        if (_test_exit.enable)
            $display("_test_exit=%x", _test_exit.addr);
        
        openStdout();
    end
    
    bit [31:0] DAddr, IAddr;
    bit [31:0] DData, IData;
    bit [3:0]  Dbe, Ibe;
    bit [2:0]  DSize, ISize;
    bit RD, WR, IF, LD, ST;
    bit MSWInt;
    bit MTInt;
    bit MEInt;
    bit reset;
    
    int int_machine_external_cnt;
    int int_machine_software_cnt;
    int int_machine_timer_cnt;
    
    always @(*) begin
        DAddr  = SysBus.DAddr;
        DData  = SysBus.DData;
        Dbe    = SysBus.Dbe;
        DSize  = SysBus.DSize;
        IAddr  = SysBus.IAddr;
        IData  = SysBus.IData;
        Ibe    = SysBus.Ibe;
        ISize  = SysBus.ISize;
        
        reset  = SysBus.reset;
        MSWInt = SysBus.irq_i[3];
        MTInt  = SysBus.irq_i[7];
        MEInt  = SysBus.irq_i[11];

        IF     = (SysBus.Ird==1);
        LD     = (SysBus.Drd==1);
        ST     = (SysBus.Dwr==1);
        RD     = IF | LD;
        WR     = ST;
    end
    
    always @(posedge SysBus.Clk) begin
        if (SysBus.Ird) begin
            // EXIT
            if (_test_exit.enable && SysBus.IAddr==_test_exit.addr) begin
                if (!SysBus.Shutdown) $display("Fetch: Exit Label");
                SysBus.Shutdown = 1;
            end
            // TRAP
            if (trap_vector.enable && SysBus.IAddr==trap_vector.addr) begin
                $display("Fetch: Trap Label");
                SysBus.Shutdown = 1;
            end
        end
        
        if (SysBus.Drd) begin
        end
        
        if (SysBus.Dwr) begin
            // STDOUT
            if (_test_stdout.enable && SysBus.DAddr==_test_stdout.addr) begin
                automatic int c = SysBus.DData&'hff;
                $write("%c", c);
                $fwrite(fd_stdout, "%c", c);
                $fflush(fd_stdout);
            end
            
            //
            // Interrupt Generation
            //
            if (_test_intc_machine_external.enable && SysBus.DAddr==_test_intc_machine_external.addr) begin
                int_machine_external_cnt = SysBus.DData;
                if (int_machine_external_cnt == 0) begin
                    // Interrupt Clear
                    $display("SysBus.irq_i[11] = 0");
                    SysBus.irq_i[11] = 0;
                end
            end  
            if (_test_intc_machine_software.enable && SysBus.DAddr==_test_intc_machine_software.addr) begin
                int_machine_software_cnt = SysBus.DData;
                if (int_machine_software_cnt == 0) begin
                    // Interrupt Clear
                    $display("SysBus.irq_i[3] = 0");
                    SysBus.irq_i[3] = 0;
                end
            end
            if (_test_intc_machine_timer.enable && SysBus.DAddr==_test_intc_machine_timer.addr) begin
                int_machine_timer_cnt = SysBus.DData;
                if (int_machine_timer_cnt == 0) begin
                    // Interrupt Clear
                    $display("SysBus.irq_i[7] = 0");
                    SysBus.irq_i[7] = 0;
                end
            end
        end
        
        // Machine External Interrupt Generation
        if (int_machine_external_cnt > 1) begin
            int_machine_external_cnt = int_machine_external_cnt - 1;
        end else if ((int_machine_external_cnt == 1) && (SysBus.irq_i[11] == 0)) begin
            $display("SysBus.irq_i[11] = 1");
            SysBus.irq_i[11] = 1;
        end 
   
        // Machine_timer Interrupt Generation
        if (int_machine_timer_cnt > 1) begin
            int_machine_timer_cnt = int_machine_timer_cnt - 1;
        end else if ((int_machine_timer_cnt == 1) && (SysBus.irq_i[7] == 0)) begin
            $display("SysBus.irq_i[7] = 1");
            SysBus.irq_i[7] = 1;        
        end

        // Machine_software Interrupt Generation
        if (int_machine_software_cnt > 1) begin
            int_machine_software_cnt = int_machine_software_cnt - 1;
        end else if ((int_machine_software_cnt == 1) && (SysBus.irq_i[3] == 0)) begin
            $display("SysBus.irq_i[3] = 1");
            SysBus.irq_i[3] = 1;        
        end
    end // always @ (posedge SysBus.Clk)
    
    final begin
        dumpSignature();
        closeStdout();
    end
endmodule
