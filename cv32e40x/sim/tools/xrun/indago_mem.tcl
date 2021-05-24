# Indago waveform probe script
ida_database -open -wave
ida_probe -log -wave=on -wave_probe_args="uvmt_cv32e40x_tb -depth all -all -memories" -sv_all_logs

# If the tracer exists, dump the string of the disassembled instruction
if { [find -scope uvmt_cv32e40x_tb.dut_wrap.cv32e40x_wrapper_i -instance tracer_i] != ""} {
    ida_probe -wave -wave_probe_args="uvmt_cv32e40x_tb.dut_wrap.cv32e40x_wrapper_i.tracer_i.insn_disas -depth 1"    
    ida_probe -wave -wave_probe_args="uvmt_cv32e40x_tb.dut_wrap.cv32e40x_wrapper_i.tracer_i.insn_regs_write -depth 1"    
}

# If the iss_wrap exists dump the string of the ISS disassembled instruction
if { [find -scope uvmt_cv32e40x_tb -instance iss_wrap] != ""} {
    ida_probe -wave -wave_probe_args="uvmt_cv32e40x_tb.iss_wrap.cpu.state.decode -depth 1"    
}

run
exit
