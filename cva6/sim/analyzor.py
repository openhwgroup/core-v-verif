# Copyright 2022 Thales DIS design services SAS
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.fr)


import re
import sys
import operator


class instr_class:
    def __init__(
        self,
        address,
        cycle_core,
        cycle_delta,
        cycle_fetch_prev,
        cycle_fetch,
        cycle_decode,
        cycle_issue,
        cycle_mmu,
        cycle_bpmiss,
        cycle_bstall,
        imiss,
        mmu,
        bpmiss,
        bstall,
        mnemo,
        stall_fetch,
        stall_decode,
        stall_issue,
        stall_core,
        to_be_printed,
    ):
        self.address = address
        self.cycle_core = cycle_core
        self.cycle_delta = cycle_delta
        self.cycle_fetch_prev = cycle_fetch
        self.cycle_fetch = cycle_fetch
        self.cycle_decode = cycle_decode
        self.cycle_issue = cycle_issue
        self.cycle_mmu = cycle_mmu
        self.cycle_bpmiss = cycle_bpmiss
        self.cycle_bstall = cycle_bstall
        self.imiss = imiss
        self.mmu = mmu
        self.bpmiss = bpmiss
        self.bstall = bstall
        self.mnemo = mnemo
        self.stall_fetch = stall_fetch
        self.stall_decode = stall_decode
        self.stall_issue = stall_issue
        self.stall_core = stall_core
        self.to_be_printed = to_be_printed

class stage_class:
    def __init__(
        self,
        l,
        stage,
        address,
        mnemo,
        cycle,
        scoreboard,
        stall,
    ):
        self.l = l
        self.stage = stage
        self.address = address
        self.mnemo = mnemo
        self.cycle = cycle
        self.scoreboard = scoreboard
        self.stall = stall


def read_trace(input_file, cycle_start, cycle_end):
    print("--------\ninput file:", input_file)
    stages = {}
    i = 0
    with open(input_file, "r") as tracefile:
        for l in tracefile:
            m = re.search("([a-z]+) +0: 0x00000000([0-9abcdef]+)( \((.*)\) (.*))?\t*cycle= +([0-9]+)\tscoreboard=([0-9]+)", l)
            if m:
                if int(m.group(6)) > cycle_start and int(m.group(6)) < cycle_end:
                    stages[i] = stage_class(l=l, stage=m.group(1), address=m.group(2), mnemo=m.group(5),
                                            cycle=int(m.group(6)), scoreboard=m.group(7), stall=0)
                    i += 1

            m = re.search("([a-zA-Z _]+): 0x(.+)\t\tcycle= +([0-9]+)", l)
            if m:
                if int(m.group(3)) > cycle_start and int(m.group(3)) < cycle_end:
                    stages[i] = stage_class(l=l, stage=m.group(1), address=m.group(2), mnemo="",
                                       cycle=m.group(3), scoreboard="", stall="")
                    i += 1
    tracefile.close()
    return stages


def write_trace(outfile, trace_instr):
    print("output file:", outfile)
    with open(outfile, "w") as fileout:
        for i in trace_instr:
            fileout.write(trace_instr[i].to_be_printed)
    fileout.close()


def main():
    input_file = sys.argv[1]

    cycle_start = 752491 # 8000277a
    cycle_end = 1119398 #"1133743" # 8000277a
    trace_stages = read_trace(input_file, cycle_start, cycle_end)
#    trace_stages = read_trace(input_file, "266", "1133743")
    trace_instr = {}
    traceout = []
    cycle_core = 0
    for i_core in trace_stages:
        if re.search("core", trace_stages[i_core].stage):
            cycle_core = trace_stages[i_core].cycle
            indice_core = str(cycle_core*10)
            if indice_core in trace_instr: indice_core = str(cycle_core*10+1)
            trace_instr[indice_core] = instr_class(
                        address = trace_stages[i_core].address,
                        cycle_core = cycle_core,
                        cycle_delta = 5000,
                        cycle_fetch_prev = 0,
                        cycle_fetch = 0,
                        cycle_decode = 0,
                        cycle_issue = 0,
                        cycle_mmu = 0,
                        cycle_bpmiss = 0,
                        cycle_bstall = 0,
                        imiss = 0,
                        mmu = "",
                        bpmiss = 0,
                        bstall = "",
                        mnemo = trace_stages[i_core].mnemo,
                        stall_fetch = 0,
                        stall_decode = 0,
                        stall_issue = 0,
                        stall_core = 0,
                        to_be_printed = "",
                        )

            instr0 = trace_instr[indice_core]
#            bpmiss0 = 0
            for i_addr in range(i_core, max(0,i_core-30), -1):
#                if (re.search("ICACHE MISS", trace_stages[i_addr].stage) and instr0.imiss == 0):
#                    instr0.imiss = instr0.imiss + 1
#                    continue
                if (re.search("MMU LOAD", trace_stages[i_addr].stage) and instr0.cycle_issue == 0):
                    instr0.mmu = "+lmmu"
                    continue
#                if (re.search("is_mispredict", trace_stages[i_addr].stage) and instr0.bpmiss == 0 and
#                    int(trace_stages[i_addr].address, 16) > int(instr0.address, 16)):
#                    instr0.bpmiss = "+bpmiss"
#                    continue
#                if (re.search("FRONTEND stall", trace_stages[i_addr].stage) and
#                    trace_stages[i_addr].address == instr0.address):
#                    instr0.fstall = instr0.fstall + 1
#                    continue
#                if (re.search("bp_valid", trace_stages[i_addr].stage) and bpmiss0 == 1):
#                    if trace_stages[i_addr].address == instr0.address:
#                        instr0.bpmiss = 1
#                    else:
#                        instr0.bpmiss = 0
#                    break
                if (re.search("fetch", trace_stages[i_addr].stage) and instr0.cycle_fetch == 0 and
                    trace_stages[i_addr].address == instr0.address):
                    instr0.cycle_fetch = trace_stages[i_addr].cycle
                    break
                if (re.search("decode", trace_stages[i_addr].stage) and instr0.cycle_decode == 0 and
                    trace_stages[i_addr].address == instr0.address):
                    instr0.cycle_decode = trace_stages[i_addr].cycle
                    continue
                if (re.search("issue", trace_stages[i_addr].stage) and instr0.cycle_issue == 0 and
                    trace_stages[i_addr].address == instr0.address):
                    instr0.cycle_issue = trace_stages[i_addr].cycle
                    continue

#            for i_addr in range(i_core+1, min(i_core+30, len(trace_stages)-1), +1):
#                if (re.search("core", trace_stages[i_addr].stage)):
#                    instr0.bstall = "+bstall+"+str(trace_stages[i_addr].cycle - instr0.cycle_core)
#                    break
#                if (re.search("FRONTEND stall", trace_stages[i_addr].stage)):
#                    instr0.cycle_bstall = instr0.cycle_bstall + 1
#                    continue


    cycle_core = cycle_start
    for cycle0 in trace_instr:
        cycle_core_prev = cycle_core
        cycle_core = trace_instr[cycle0].cycle_core
        trace_instr[cycle0].cycle_delta = cycle_core - cycle_core_prev

    for cycle0 in trace_instr:
        if ("beq " in trace_instr[cycle0].mnemo or
            "bne " in trace_instr[cycle0].mnemo or
            "blt " in trace_instr[cycle0].mnemo or
            "bge " in trace_instr[cycle0].mnemo or
            "bgeu " in trace_instr[cycle0].mnemo or
            "bltu " in trace_instr[cycle0].mnemo or
            "beqz " in trace_instr[cycle0].mnemo or
            "bnez " in trace_instr[cycle0].mnemo or
            "blez " in trace_instr[cycle0].mnemo or
            "bgez " in trace_instr[cycle0].mnemo or
            "bltz " in trace_instr[cycle0].mnemo or
            "bgtz " in trace_instr[cycle0].mnemo or
            "bgt " in trace_instr[cycle0].mnemo or
            "ble " in trace_instr[cycle0].mnemo or
            "bgtu " in trace_instr[cycle0].mnemo or
            "bleu " in trace_instr[cycle0].mnemo or
            "bgt " in trace_instr[cycle0].mnemo or
            "bgt " in trace_instr[cycle0].mnemo or
            "jal " in trace_instr[cycle0].mnemo or
            "jalr " in trace_instr[cycle0].mnemo or
            "j " in trace_instr[cycle0].mnemo or
            "jr " in trace_instr[cycle0].mnemo or
            "ret " in trace_instr[cycle0].mnemo or
            "auipc " in trace_instr[cycle0].mnemo or
            "tail " in trace_instr[cycle0].mnemo):
            cycle0_next = str(int(cycle0)+1)
            while(cycle0_next not in trace_instr):
                cycle0_next = str(int(cycle0_next)+1)
            trace_instr[cycle0].cycle_bstall = trace_instr[cycle0_next].cycle_delta - 1
            trace_instr[cycle0].bstall = "+bstall+"+str(trace_instr[cycle0_next].cycle_delta - 1)

    for cycle0 in trace_instr:
        if trace_instr[cycle0].cycle_delta == 0 or trace_instr[cycle0].cycle_delta == 1:
            trace_instr[cycle0].mmu = ""
        if trace_instr[cycle0].mmu == "+lmmu":
            trace_instr[cycle0].cycle_mmu = trace_instr[cycle0].cycle_core - trace_instr[cycle0].cycle_issue - 3
            trace_instr[cycle0].mmu = "+lmmu+"+str(trace_instr[cycle0].cycle_mmu)

    for cycle0 in trace_instr:
        trace_instr[cycle0].to_be_printed="#{}+{} 0x{}: decode+{} issue+{} core+{}{}{} - {}".format(
              trace_instr[cycle0].cycle_core,
              trace_instr[cycle0].cycle_delta,
              trace_instr[cycle0].address,
              str(trace_instr[cycle0].cycle_decode - trace_instr[cycle0].cycle_fetch),
              str(trace_instr[cycle0].cycle_issue - trace_instr[cycle0].cycle_decode),
              str(trace_instr[cycle0].cycle_core - trace_instr[cycle0].cycle_issue - trace_instr[cycle0].cycle_mmu),
              trace_instr[cycle0].mmu,
              trace_instr[cycle0].bstall,
              trace_instr[cycle0].mnemo)

    cycle_number = cycle_end - cycle_start
    print("cycle number             = %s" % str(cycle_number))
    print("Coremark/MHz             = %s" % str(1000000/cycle_number))
    print("instruction number       = %s" % str(len(trace_instr)))

    impact = 0
    for cycle0 in trace_instr:
            impact = impact + trace_instr[cycle0].cycle_mmu
    print("load mmu impact          = %s = %s per cent of cycle number" % (str(impact), str(impact / cycle_number * 100)))

    impact = 0
    for cycle0 in trace_instr:
            impact = impact + trace_instr[cycle0].cycle_bstall
    print("branch fetch impact      = %s = %s per cent of cycle number" % (str(impact), str(impact / cycle_number * 100)))

    impact = 0
    for cycle0 in trace_instr:
        if ("lw " in trace_instr[cycle0].mnemo or
            "lh " in trace_instr[cycle0].mnemo or
            "lb " in trace_instr[cycle0].mnemo or
            "lbu " in trace_instr[cycle0].mnemo or
            "lhu " in trace_instr[cycle0].mnemo):
            impact = impact + trace_instr[cycle0].cycle_core - trace_instr[cycle0].cycle_issue - trace_instr[cycle0].cycle_mmu - 1
    print("load execution impact    = %s = %s per cent of cycle number" % (str(impact), str(impact / cycle_number * 100)))

    impact = 0
    for cycle0 in trace_instr:
        if ("sw " in trace_instr[cycle0].mnemo or
            "sh " in trace_instr[cycle0].mnemo or
            "sb " in trace_instr[cycle0].mnemo):
            impact = impact + trace_instr[cycle0].cycle_core - trace_instr[cycle0].cycle_issue - trace_instr[cycle0].cycle_mmu - 1
    print("store execution impact   = %s = %s per cent of cycle number" % (str(impact), str(impact / cycle_number * 100)))

#    impact = 0
#    for cycle0 in trace_instr:
#        if trace_instr[cycle0].imiss != 0:
#            impact = impact + trace_instr[cycle0].imiss
#            trace_instr[cycle0].to_be_printed += "imiss "
#    print("imiss impact             = %s = %s per cent of cycle number" % (str(impact), str(impact / cycle_number * 100)))

#    impact = 0
#    for cycle0 in trace_instr:
#        if int(trace_instr[cycle0].fstall) != 0:
#            impact = impact + int(trace_instr[cycle0].fstall)
#            trace_instr[cycle0].to_be_printed += "fstall "
#    print("fetch stall impact       = %s = %s per cent of cycle number" % (str(impact), str(impact / cycle_number * 100)))

    for cycle0 in trace_instr:
        trace_instr[cycle0].to_be_printed += "\n"
        if int(trace_instr[cycle0].cycle_delta) > 9:
            print(trace_instr[cycle0].to_be_printed.split("\n"))

    write_trace("traceout.log", trace_instr)

if __name__ == "__main__":
    main()


