Makefile:14: must set CVA6_REPO_DIR to point at the root of CVA6 sources and CVA6_TB_DIR to point here -- doing it for you...
make -C /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6 vcs_build target=cv32a60x defines=WT_DCACHE+RVFI_TRACE+RVFI_MEM
make[1]: Entering directory `/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6'
Makefile:133: XCELIUM_HOME not set which is necessary for compiling DPIs when using XCELIUM
mkdir -p work-dpi
g++ -shared -fPIC -std=c++0x -Bsymbolic -I/include -I/home/VCS2023/vcs/S-2021.09-SP2-7//include -I/home/t0268396/Desktop/sk/cva6-tools/toolchain/include -I/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/tools/spike//include  -std=c++11 -I../corev_apu/tb/dpi -O3 -c corev_apu/tb/dpi/SimDTM.cc -o work-dpi/SimDTM.o
mkdir -p work-dpi
g++ -shared -fPIC -std=c++0x -Bsymbolic -I/include -I/home/VCS2023/vcs/S-2021.09-SP2-7//include -I/home/t0268396/Desktop/sk/cva6-tools/toolchain/include -I/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/tools/spike//include  -std=c++11 -I../corev_apu/tb/dpi -O3 -c corev_apu/tb/dpi/elfloader.cc -o work-dpi/elfloader.o
mkdir -p work-dpi
g++ -shared -fPIC -std=c++0x -Bsymbolic -I/include -I/home/VCS2023/vcs/S-2021.09-SP2-7//include -I/home/t0268396/Desktop/sk/cva6-tools/toolchain/include -I/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/tools/spike//include  -std=c++11 -I../corev_apu/tb/dpi -O3 -c corev_apu/tb/dpi/msim_helper.cc -o work-dpi/msim_helper.o
mkdir -p work-dpi
g++ -shared -fPIC -std=c++0x -Bsymbolic -I/include -I/home/VCS2023/vcs/S-2021.09-SP2-7//include -I/home/t0268396/Desktop/sk/cva6-tools/toolchain/include -I/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/tools/spike//include  -std=c++11 -I../corev_apu/tb/dpi -O3 -c corev_apu/tb/dpi/remote_bitbang.cc -o work-dpi/remote_bitbang.o
mkdir -p work-dpi
g++ -shared -fPIC -std=c++0x -Bsymbolic -I/include -I/home/VCS2023/vcs/S-2021.09-SP2-7//include -I/home/t0268396/Desktop/sk/cva6-tools/toolchain/include -I/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/tools/spike//include  -std=c++11 -I../corev_apu/tb/dpi -O3 -c corev_apu/tb/dpi/SimJTAG.cc -o work-dpi/SimJTAG.o
mkdir -p work-dpi
# Compile C-code and generate .so file
g++ -shared -m64 -o work-dpi/ariane_dpi.so work-dpi/SimDTM.o work-dpi/elfloader.o work-dpi/msim_helper.o work-dpi/remote_bitbang.o work-dpi/SimJTAG.o -L/home/t0268396/Desktop/sk/cva6-tools/toolchain/lib -L/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/tools/spike//lib -Wl,-rpath,/home/t0268396/Desktop/sk/cva6-tools/toolchain/lib -Wl,-rpath,/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/tools/spike//lib -lfesvr
mkdir -p work-vcs
cd work-vcs &&\
vlogan  -full64 -nc -sverilog +define+WT_DCACHE+RVFI_TRACE+RVFI_MEM -f ../core/Flist.cva6 &&\
vlogan  -full64 -nc -sverilog +define+WT_DCACHE+RVFI_TRACE+RVFI_MEM /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/register_interface/src/reg_intf.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/rvfi_pkg.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_soc_pkg.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dm_pkg.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_axi_soc_pkg.sv +incdir+core/include/+/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dpi &&\
vhdlan  -full64 -nc /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/apb_uart.vhd /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/uart_transmitter.vhd /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/uart_interrupt.vhd /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/slib_mv_filter.vhd /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/slib_input_filter.vhd /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/slib_counter.vhd /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/uart_receiver.vhd /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/slib_input_sync.vhd /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/slib_edge_detect.vhd /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/slib_clock_div.vhd /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/slib_fifo.vhd /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/uart_baudgen.vhd &&\
vlogan  -full64 -nc -sverilog -assert svaext +define+WT_DCACHE+RVFI_TRACE+RVFI_MEM /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/axi_adapter.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/bootrom/bootrom.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/bootrom/dromajo_bootrom.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/clint/axi_lite_interface.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/clint/clint.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi2apb/src/axi2apb_wrap.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi2apb/src/axi2apb.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi2apb/src/axi2apb_64_32.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_timer/apb_timer.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_timer/timer.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_w_buffer.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_b_buffer.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_slice_wrap.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_slice.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_single_slice.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_ar_buffer.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_r_buffer.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_aw_buffer.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_amos.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_atomics.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/src/axi_riscv_atomics/src/axi_res_tbl.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_lrsc_wrap.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_amos_alu.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_lrsc.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_atomics_wrap.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/axi_mem_if/src/axi2mem.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/rv_plic/rtl/rv_plic_target.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/rv_plic/rtl/rv_plic_gateway.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/rv_plic/rtl/plic_regmap.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/rv_plic/rtl/plic_top.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dmi_cdc.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dmi_jtag.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dmi_jtag_tap.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dm_csrs.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dm_mem.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dm_sba.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dm_top.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/debug_rom/debug_rom.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/register_interface/src/apb_to_reg.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_multicut.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/rstgen_bypass.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/rstgen.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/stream_mux.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/stream_demux.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/exp_backoff.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/addr_decode.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/stream_register.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_cut.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_join.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_delayer.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_to_axi_lite.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_id_prepend.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_atop_filter.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_err_slv.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_mux.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_demux.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_xbar.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/cdc_2phase.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/spill_register_flushable.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/spill_register.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/stream_arbiter.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/stream_arbiter_flushable.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/deprecated/fifo_v1.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/deprecated/fifo_v2.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/stream_delay.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/lfsr_16bit.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/tech_cells_generic/src/deprecated/cluster_clk_cells.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/tech_cells_generic/src/deprecated/pulp_clk_cells.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/tech_cells_generic/src/rtl/tc_clk.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_testharness.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_peripherals.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/rvfi_tracer.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/common/uart.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/common/SimDTM.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/common/SimJTAG.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/mmu_sv32/cva6_mmu_sv32.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/mmu_sv32/cva6_ptw_sv32.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/mmu_sv32/cva6_tlb_sv32.sv +incdir+../vendor/pulp-platform/common_cells/include/+../vendor/pulp-platform/axi/include/+../corev_apu/register_interface/include/ &&\
vlogan  -full64 -nc -sverilog -ntb_opts uvm-1.2 &&\
vlogan  -full64 -nc -sverilog -ntb_opts uvm-1.2 /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_tb.sv /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_testharness.sv +define+WT_DCACHE+RVFI_TRACE+RVFI_MEM +incdir+../vendor/pulp-platform/axi/include/ &&\
vcs  -full64 -timescale=1ns/1ns -ntb_opts uvm-1.2 work.ariane_tb -error="IWNF"
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpga-support/rtl/SyncDpRam.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpga-support/rtl/AsyncDpRam.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpga-support/rtl/AsyncThreePortRam.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/include/cv32a60x_config_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/include/riscv_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/include/ariane_dm_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/include/ariane_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/include/ariane_rvfi_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/include/ariane_axi_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/include/wt_cache_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/include/std_cache_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/include/axi_intf.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/include/instr_tracer_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/include/cvxif_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cvxif_example/include/cvxif_instr_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cvxif_fu.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cvxif_example/cvxif_example_coprocessor.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cvxif_example/instr_decoder.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/cf_math_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/fifo_v3.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/lfsr.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/lzc.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/rr_arb_tree.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/shift_reg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/unread.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/popcount.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/exp_backoff.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/counter.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/delta_counter.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_cast_multi.sv'
Parsing included file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/include/common_cells/registers.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_cast_multi.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_classifier.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_divsqrt_multi.sv'
Parsing included file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/include/common_cells/registers.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_divsqrt_multi.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_fma_multi.sv'
Parsing included file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/include/common_cells/registers.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_fma_multi.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_fma.sv'
Parsing included file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/include/common_cells/registers.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_fma.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_noncomp.sv'
Parsing included file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/include/common_cells/registers.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_noncomp.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_opgroup_block.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_opgroup_fmt_slice.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_opgroup_multifmt_slice.sv'
Parsing included file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/include/common_cells/registers.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_opgroup_multifmt_slice.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_rounding.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpnew_top.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpu_div_sqrt_mvp/hdl/defs_div_sqrt_mvp.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpu_div_sqrt_mvp/hdl/control_mvp.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpu_div_sqrt_mvp/hdl/div_sqrt_top_mvp.sv'

Note-[SV-LCM-PPWI] Package previously wildcard imported
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpu_div_sqrt_mvp/hdl/div_sqrt_top_mvp.sv, 35
$unit
  Package 'defs_div_sqrt_mvp' already wildcard imported. 
  Ignoring defs_div_sqrt_mvp::*
  See the SystemVerilog LRM(1800-2005), section 19.2.1.

Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpu_div_sqrt_mvp/hdl/iteration_div_sqrt_mvp.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpu_div_sqrt_mvp/hdl/norm_div_sqrt_mvp.sv'

Note-[SV-LCM-PPWI] Package previously wildcard imported
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpu_div_sqrt_mvp/hdl/norm_div_sqrt_mvp.sv, 44
$unit
  Package 'defs_div_sqrt_mvp' already wildcard imported. 
  Ignoring defs_div_sqrt_mvp::*
  See the SystemVerilog LRM(1800-2005), section 19.2.1.

Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpu_div_sqrt_mvp/hdl/nrbd_nrsc_mvp.sv'

Note-[SV-LCM-PPWI] Package previously wildcard imported
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpu_div_sqrt_mvp/hdl/nrbd_nrsc_mvp.sv, 34
$unit
  Package 'defs_div_sqrt_mvp' already wildcard imported. 
  Ignoring defs_div_sqrt_mvp::*
  See the SystemVerilog LRM(1800-2005), section 19.2.1.

Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpu_div_sqrt_mvp/hdl/preprocess_mvp.sv'

Note-[SV-LCM-PPWI] Package previously wildcard imported
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/fpnew/src/fpu_div_sqrt_mvp/hdl/preprocess_mvp.sv, 35
$unit
  Package 'defs_div_sqrt_mvp' already wildcard imported. 
  Ignoring defs_div_sqrt_mvp::*
  See the SystemVerilog LRM(1800-2005), section 19.2.1.

Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/ariane.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cva6.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/alu.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/fpu_wrap.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/branch_unit.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/compressed_decoder.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/controller.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/csr_buffer.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/csr_regfile.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/decoder.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/ex_stage.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/instr_realign.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/id_stage.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/issue_read_operands.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/issue_stage.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/load_unit.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/load_store_unit.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/lsu_bypass.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/mult.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/multiplier.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/serdiv.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/perf_counters.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/ariane_regfile_ff.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/ariane_regfile_fpga.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/re_name.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/scoreboard.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/store_buffer.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/amo_buffer.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/store_unit.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/commit_stage.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/axi_shim.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/frontend/btb.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/frontend/bht.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/frontend/ras.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/frontend/instr_scan.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/frontend/instr_queue.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/frontend/frontend.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cache_subsystem/wt_dcache_ctrl.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cache_subsystem/wt_dcache_mem.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cache_subsystem/wt_dcache_missunit.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cache_subsystem/wt_dcache_wbuffer.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cache_subsystem/wt_dcache.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cache_subsystem/cva6_icache.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cache_subsystem/wt_cache_subsystem.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cache_subsystem/wt_axi_adapter.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/pmp/src/pmp.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/pmp/src/pmp_entry.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/common/local/util/instr_tracer_if.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/common/local/util/instr_tracer.sv'
Parsing included file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/common/local/util/ex_trace_item.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/common/local/util/instr_tracer.sv'.
Parsing included file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/common/local/util/instr_trace_item.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/common/local/util/instr_tracer.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/common/local/util/tc_sram_wrapper.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/tech_cells_generic/src/rtl/tc_sram.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/common/local/util/sram.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/mmu_sv39/mmu.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/mmu_sv39/ptw.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/mmu_sv39/tlb.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/mmu_sv32/cva6_mmu_sv32.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/mmu_sv32/cva6_ptw_sv32.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/mmu_sv32/cva6_tlb_sv32.sv'
CPU time: .305 seconds to compile
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/register_interface/src/reg_intf.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/rvfi_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_soc_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dm_pkg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_axi_soc_pkg.sv'
CPU time: .074 seconds to compile
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/apb_uart.vhd'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/uart_transmitter.vhd'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/uart_interrupt.vhd'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/slib_mv_filter.vhd'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/slib_input_filter.vhd'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/slib_counter.vhd'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/uart_receiver.vhd'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/slib_input_sync.vhd'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/slib_edge_detect.vhd'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/slib_clock_div.vhd'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/slib_fifo.vhd'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_uart/src/uart_baudgen.vhd'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/axi_adapter.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/bootrom/bootrom.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/bootrom/dromajo_bootrom.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/clint/axi_lite_interface.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/clint/clint.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi2apb/src/axi2apb_wrap.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi2apb/src/axi2apb.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi2apb/src/axi2apb_64_32.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_timer/apb_timer.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/apb_timer/timer.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_w_buffer.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_b_buffer.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_slice_wrap.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_slice.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_single_slice.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_ar_buffer.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_r_buffer.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/fpga/src/axi_slice/src/axi_aw_buffer.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_amos.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_atomics.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/src/axi_riscv_atomics/src/axi_res_tbl.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_lrsc_wrap.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_amos_alu.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_lrsc.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/src/axi_riscv_atomics/src/axi_riscv_atomics_wrap.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/axi_mem_if/src/axi2mem.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/rv_plic/rtl/rv_plic_target.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/rv_plic/rtl/rv_plic_gateway.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/rv_plic/rtl/plic_regmap.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/rv_plic/rtl/plic_top.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dmi_cdc.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dmi_jtag.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dmi_jtag_tap.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dm_csrs.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dm_mem.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dm_sba.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/src/dm_top.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/riscv-dbg/debug_rom/debug_rom.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/register_interface/src/apb_to_reg.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_multicut.sv'
Parsing included file '../vendor/pulp-platform/axi/include/axi/assign.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_multicut.sv'.
Parsing included file '../vendor/pulp-platform/axi/include/axi/typedef.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_multicut.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/rstgen_bypass.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/rstgen.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/stream_mux.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/stream_demux.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/exp_backoff.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/addr_decode.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/stream_register.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_cut.sv'
Parsing included file '../vendor/pulp-platform/axi/include/axi/assign.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_cut.sv'.
Parsing included file '../vendor/pulp-platform/axi/include/axi/typedef.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_cut.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_join.sv'
Parsing included file '../vendor/pulp-platform/axi/include/axi/assign.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_join.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_delayer.sv'
Parsing included file '../vendor/pulp-platform/axi/include/axi/typedef.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_delayer.sv'.
Parsing included file '../vendor/pulp-platform/axi/include/axi/assign.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_delayer.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_to_axi_lite.sv'
Parsing included file '../vendor/pulp-platform/axi/include/axi/assign.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_to_axi_lite.sv'.
Parsing included file '../vendor/pulp-platform/axi/include/axi/typedef.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_to_axi_lite.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_id_prepend.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_atop_filter.sv'
Parsing included file '../vendor/pulp-platform/axi/include/axi/assign.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_atop_filter.sv'.
Parsing included file '../vendor/pulp-platform/axi/include/axi/typedef.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_atop_filter.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_err_slv.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_mux.sv'
Parsing included file '../vendor/pulp-platform/common_cells/include/common_cells/registers.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_mux.sv'.
Parsing included file '../vendor/pulp-platform/axi/include/axi/assign.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_mux.sv'.
Parsing included file '../vendor/pulp-platform/axi/include/axi/typedef.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_mux.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_demux.sv'
Parsing included file '../vendor/pulp-platform/common_cells/include/common_cells/registers.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_demux.sv'.
Parsing included file '../vendor/pulp-platform/axi/include/axi/assign.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_demux.sv'.
Parsing included file '../vendor/pulp-platform/axi/include/axi/typedef.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_demux.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_xbar.sv'
Parsing included file '../vendor/pulp-platform/axi/include/axi/assign.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_xbar.sv'.
Parsing included file '../vendor/pulp-platform/axi/include/axi/typedef.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/axi/src/axi_xbar.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/cdc_2phase.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/spill_register_flushable.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/spill_register.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/stream_arbiter.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/stream_arbiter_flushable.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/deprecated/fifo_v1.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/deprecated/fifo_v2.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/stream_delay.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/common_cells/src/lfsr_16bit.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/tech_cells_generic/src/deprecated/cluster_clk_cells.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/tech_cells_generic/src/deprecated/pulp_clk_cells.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/vendor/pulp-platform/tech_cells_generic/src/rtl/tc_clk.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_testharness.sv'
Parsing included file '../vendor/pulp-platform/axi/include/axi/assign.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_testharness.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_peripherals.sv'
Parsing included file '../corev_apu/register_interface/include/register_interface/assign.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_peripherals.sv'.
Parsing included file '../corev_apu/register_interface/include/register_interface/typedef.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_peripherals.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/rvfi_tracer.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/common/uart.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/common/SimDTM.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/common/SimJTAG.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/mmu_sv32/cva6_mmu_sv32.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/mmu_sv32/cva6_ptw_sv32.sv'
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/mmu_sv32/cva6_tlb_sv32.sv'
CPU time: .197 seconds to compile
Parsing design file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_pkg.sv'
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_version_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_global_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/snps_macros.svp'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_message_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_phase_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_object_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_printer_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_tlm_defines.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm_imps.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_tlm_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_sequence_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_callback_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_reg_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_deprecated_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_pkg.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/directc/uvm_directc.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/directc/uvm_seed.vh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/directc/uvm_directc.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_pkg.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dpi/uvm_dpi.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dpi/uvm_hdl.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dpi/uvm_dpi.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dpi/uvm_svcmd_dpi.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dpi/uvm_dpi.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dpi/uvm_regex.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dpi/uvm_dpi.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_pkg.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_coreservice.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_version.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_object_globals.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_misc.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_object.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_pool.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_queue.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_factory.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_registry.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_spell_chkr.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_resource.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_resource_specializations.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_resource_db.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_config_db.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_printer.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_comparer.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_packer.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_links.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_tr_database.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_tr_stream.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_recorder.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_event_callback.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_event.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_barrier.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_callback.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_callback.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_report_message.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_report_catcher.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_report_server.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_report_handler.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_report_object.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_transaction.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_phase.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_domain.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_bottomup_phase.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_topdown_phase.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_task_phase.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_common_phases.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_runtime_phases.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_component.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_root.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_component.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_objection.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_heartbeat.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_globals.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_cmdline_processor.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_traversal.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_base.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_pkg.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dap/uvm_dap.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dap/uvm_set_get_dap_base.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dap/uvm_dap.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dap/uvm_simple_lock_dap.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dap/uvm_dap.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dap/uvm_get_to_lock_dap.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dap/uvm_dap.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dap/uvm_set_before_get_dap.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dap/uvm_dap.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_pkg.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm_ifs.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_sqr_ifs.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_port_base.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm_imps.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_imps.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_ports.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_exports.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_analysis_port.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm_fifo_base.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm_fifos.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm_req_rsp.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_sqr_connections.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_pkg.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_comps.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_pair.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_comps.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_policies.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_comps.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_in_order_comparator.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_comps.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_algorithmic_comparator.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_comps.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_random_stimulus.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_comps.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_subscriber.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_comps.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_monitor.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_comps.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_driver.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_comps.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_push_driver.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_comps.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_scoreboard.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_comps.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_agent.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_comps.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_env.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_comps.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_test.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/comps/uvm_comps.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_pkg.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_seq.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_sequence_item.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_seq.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_sequencer_base.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_seq.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_sequencer_analysis_fifo.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_seq.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_sequencer_param_base.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_seq.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_sequencer.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_seq.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_push_sequencer.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_seq.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_sequence_base.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_seq.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_sequence.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_seq.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_sequence_library.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_seq.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_sequence_builtin.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/seq/uvm_seq.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_pkg.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2_time.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2_generic_payload.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2_ifs.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2_imps.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2_ports.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2_exports.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2_sockets_base.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2_sockets.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm2/uvm_tlm2.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_pkg.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_item.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_adapter.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_predictor.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_sequence.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_cbs.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_backdoor.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_field.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_vreg_field.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_indirect.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_fifo.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_file.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_mem_mam.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_vreg.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_mem.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_map.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_block.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/sequences/uvm_reg_hw_reset_seq.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/sequences/uvm_reg_bit_bash_seq.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/sequences/uvm_mem_walk_seq.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/sequences/uvm_mem_access_seq.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/sequences/uvm_reg_access_seq.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/sequences/uvm_reg_mem_shared_access_seq.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/sequences/uvm_reg_mem_built_in_seq.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/sequences/uvm_reg_mem_hdl_paths_seq.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/snps_uvm_reg_bank.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/reg/uvm_reg_model.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_pkg.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/vcs/vcs_uvm_alt.sv'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_pkg.sv'.
Parsing design file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/vcs/uvm_custom_install_vcs_recorder.sv'
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/vcs/msglog.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/vcs/uvm_custom_install_vcs_recorder.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/vcs/uvm_msglog_report_server.sv'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/vcs/uvm_custom_install_vcs_recorder.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/vcs/uvm_vcs_recorder.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/vcs/uvm_vcs_tr_database.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/vcs/uvm_vcs_tr_stream.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/vcs/uvm_vcs_tr_database.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/vcs/uvm_vcs_recorder.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/vcs/uvm_custom_install_vcs_recorder.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/vcs/uvm_vcs_record_interface.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_global_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/vcs/uvm_vcs_record_interface.sv'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/vcs/uvm_custom_install_vcs_recorder.sv'.
Parsing design file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_custom_install_verdi_recorder.sv'
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_custom_install_verdi_recorder.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_verdi_recorder.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_verdi_pli_base.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_verdi_recorder.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_verdi_tr_database.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_verdi_tr_stream.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_verdi_tr_database.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_verdi_recorder.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_custom_install_verdi_recorder.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_verdi_reg_map_recording.sv'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_custom_install_verdi_recorder.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_verdi_message_catcher.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_verdi_pli_base.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_verdi_message_catcher.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_custom_install_verdi_recorder.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_verdi_factory.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_custom_install_verdi_recorder.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/./dpi/uvm_verdi_dpi.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_custom_install_verdi_recorder.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_verdi_reg_recording.sv'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_custom_install_verdi_recorder.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/verdi_trans_recorder_dpi.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_custom_install_verdi_recorder.sv'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_verdi_pli.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/verdi/uvm_custom_install_verdi_recorder.sv'.
CPU time: .742 seconds to compile
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_tb.sv'
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_version_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_global_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/snps_macros.svp'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_message_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_phase_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_object_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_printer_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_tlm_defines.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/tlm1/uvm_tlm_imps.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_tlm_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_sequence_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_callback_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_reg_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Parsing included file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/macros/uvm_deprecated_defines.svh'.
Back to file '/home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/uvm_macros.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_tb.sv'.
Parsing design file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_testharness.sv'
Parsing included file '../vendor/pulp-platform/axi/include/axi/assign.svh'.
Back to file '/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_testharness.sv'.
CPU time: .176 seconds to compile
Doing common elaboration 
                         Chronologic VCS (TM)
      Version S-2021.09-SP2-7_Full64 -- Thu Mar 23 02:24:47 2023

                    Copyright (c) 1991 - 2023 Synopsys, Inc.
   This software and the associated documentation are proprietary to Synopsys,
 Inc. This software may only be used in accordance with the terms and conditions
 of a written license agreement with Synopsys, Inc. All other use, reproduction,
   or distribution of this software is strictly prohibited.  Licensed Products
     communicate with Synopsys servers for the purpose of providing software
    updates, detecting software piracy and verifying that customers are using
    Licensed Products in conformity with the applicable License Key for such
  Licensed Products. Synopsys will use information gathered in connection with
    this process to deliver software updates and pursue software pirates and
                                   infringers.

 Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
            Inclusivity and Diversity" (Refer to article 000036315 at
                        https://solvnetplus.synopsys.com)

Top Level Modules:
       ariane_tb
TimeScale is 1 ns / 1 ns

Warning-[IAVCVF-W] Incorrect argument to void cast
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_tb.sv, 142
ariane_tb, "void'($unit::read_section(address, buffer));"
  Void function '$unit::read_section(address, buffer)' cannot be used as the 
  argument to cast operator.
  Please refer to Section 6.24.1 'Cast operator' of the SystemVerilog LRM Std.
  1800-2012.


Warning-[PCWM-W] Port connection width mismatch
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_testharness.sv, 292
"axi_adapter #(AXI_DATA_WIDTH, , , ariane_axi_soc::AddrWidth, ariane_axi_soc::DataWidth, ariane_soc::IdWidth, req_t, resp_t, , ) i_dm_axi_master( .clk_i (clk_i),  .rst_ni (rst_ni),  .req_i (dm_master_req),  .type_i (SINGLE_REQ),  .amo_i (AMO_NONE),  .gnt_o (dm_master_gnt),  .addr_i (dm_master_add),  .we_i (dm_master_we),  .wdata_i (dm_master_wdata),  .be_i (dm_master_be),  .size_i (2'b11),  .id_i ('0),  .valid_o (dm_master_r_valid),  .rdata_o (dm_master_r_rdata),  .axi_req_o (dm_axi_m_req),  .axi_resp_i (dm_axi_m_resp));"
  The following 64-bit expression is connected to 32-bit port "addr_i" of 
  module "axi_adapter", instance "i_dm_axi_master".
  Expression: dm_master_add
  Instantiated module defined at: 
  "/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/axi_adapter.sv",
  19
  Use +lint=PCWM for more details.


Warning-[PCWM-W] Port connection width mismatch
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_testharness.sv, 622
"ariane #(6434'b0000000000000000000000000000100000000000000000000000000010000000000000000000000000000010000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 ... "
  The following 64-bit expression is connected to 32-bit port "boot_addr_i" of
  module "ariane", instance "i_ariane".
  Expression: ROMBase
  Instantiated module defined at: 
  "/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/ariane.sv",
  16
  Use +lint=PCWM for more details.


Warning-[PCWM-W] Port connection width mismatch
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_testharness.sv, 622
"ariane #(6434'b0000000000000000000000000000100000000000000000000000000010000000000000000000000000000010000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 ... "
  The following 64-bit expression is connected to 32-bit port "hart_id_i" of 
  module "ariane", instance "i_ariane".
  Expression: {56'b0, hart_id}
  Instantiated module defined at: 
  "/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/ariane.sv",
  16
  Use +lint=PCWM for more details.


Warning-[SIOB] Select index out of bounds
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cvxif_example/cvxif_example_coprocessor.sv, 146
"req_o.req.rs[2]"
  The select index is out of declared bounds : [1:0].
  In module instance : gen_example_coprocessor.i_cvxif_coprocessor 
  In module : cvxif_example_coprocessor.


Warning-[SIOB] Select index out of bounds
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/issue_read_operands.sv, 495
"rdata[2]"
  The select index is out of declared bounds : [1:0].
  In module instance : i_issue_read_operands 
  In module : issue_read_operands.


Warning-[SIOB] Select index out of bounds
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cvxif_fu.sv, 47
"cvxif_req_o.x_issue_req.rs[2]"
  The select index is out of declared bounds : [1:0].
  In module instance : gen_cvxif.cvxif_fu_i 
  In module : cvxif_fu.


Warning-[SIOB] Select index out of bounds
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/alu.sv, 292
"fu_data_i.operand_a[63:56]"
  The select index is out of declared bounds : [31:0].
  In module instance : alu_i 
  In module : alu.


Warning-[SIOB] Select index out of bounds
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/alu.sv, 292
"fu_data_i.operand_a[55:48]"
  The select index is out of declared bounds : [31:0].
  In module instance : alu_i 
  In module : alu.


Warning-[SIOB] Select index out of bounds
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/alu.sv, 292
"fu_data_i.operand_a[47:40]"
  The select index is out of declared bounds : [31:0].
  In module instance : alu_i 
  In module : alu.


Warning-[SIOB] Select index out of bounds
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/alu.sv, 292
"fu_data_i.operand_a[39:32]"
  The select index is out of declared bounds : [31:0].
  In module instance : alu_i 
  In module : alu.


Warning-[SIOB] Select index out of bounds
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/alu.sv, 293
"fu_data_i.operand_a[39:32]"
  The select index is out of declared bounds : [31:0].
  In module instance : alu_i 
  In module : alu.


Warning-[SIOB] Select index out of bounds
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/alu.sv, 293
"fu_data_i.operand_a[47:40]"
  The select index is out of declared bounds : [31:0].
  In module instance : alu_i 
  In module : alu.


Warning-[SIOB] Select index out of bounds
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/alu.sv, 293
"fu_data_i.operand_a[55:48]"
  The select index is out of declared bounds : [31:0].
  In module instance : alu_i 
  In module : alu.


Warning-[SIOB] Select index out of bounds
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/alu.sv, 293
"fu_data_i.operand_a[63:56]"
  The select index is out of declared bounds : [31:0].
  In module instance : alu_i 
  In module : alu.


Warning-[SIOB] Select index out of bounds
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cache_subsystem/wt_dcache_wbuffer.sv, 486
"wbuffer_d[wr_ptr].user[(k * 8)+:8]"
  The select index is out of declared bounds : [0:0].
  In module instance : i_wt_dcache_wbuffer 
  In module : wt_dcache_wbuffer.


Warning-[SIOB] Select index out of bounds
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/cache_subsystem/wt_dcache_wbuffer.sv, 486
"req_port_i.data_wuser[(k * 8)+:8]"
  The select index is out of declared bounds : [0:0].
  In module instance : i_wt_dcache_wbuffer 
  In module : wt_dcache_wbuffer.


Warning-[SIOB] Select index out of bounds
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/core/pmp/src/pmp.sv, 37
"conf_addr_i[(0 - 1)]"
  The select index is out of declared bounds : [15:0].
  In module instance : i_pmp_ptw i_pmp_if i_pmp_data 
  In module : pmp.


Note-[SIMU-RESOLUTION] Simulation time resolution
  Simulation time resolution is 1 NS


Warning-[DRTZ] Detect delay value roundoff to 0
  Delay from design or SDF file roundoff to 0 based on timescale
  Please use switch -diag timescale to dump detailed information.

Notice: Ports coerced to inout, use -notice for details
Starting vcs inline pass...

82 modules and 0 UDP read.
recompiling package vcs_paramclassrepository
recompiling package uvm_pkg
recompiling package cva6_config_pkg
recompiling package riscv
recompiling package ariane_dm_pkg
recompiling package ariane_pkg
recompiling module ariane_tb
recompiling package _vcs_DPI_package
recompiling package ariane_soc
recompiling package dm
recompiling package axi_pkg
recompiling package ariane_axi
recompiling package ariane_rvfi_pkg
recompiling package ariane_axi_soc
recompiling package instr_tracer_pkg
recompiling package defs_div_sqrt_mvp
recompiling module AXI_BUS
recompiling module rstgen
recompiling module SimJTAG
recompiling module dmi_jtag
recompiling module fifo_v3
recompiling module axi2mem
recompiling module axi_adapter
recompiling module bootrom
recompiling module axi_err_slv
recompiling module counter
recompiling module delta_counter
recompiling module axi_riscv_atomics_wrap
recompiling module axi_delayer_intf
recompiling module sram
recompiling module clint
recompiling module ariane_peripherals
recompiling module REG_BUS
recompiling module axi2apb_64_32
recompiling module axi_single_slice
recompiling module uart_bus
recompiling package cvxif_pkg
recompiling module ariane
recompiling module frontend
recompiling module id_stage
recompiling module issue_stage
recompiling module re_name
recompiling module rr_arb_tree
recompiling module alu
recompiling module branch_unit
recompiling module csr_buffer
recompiling module mult
recompiling package cf_math_pkg
recompiling module lzc
recompiling module commit_stage
50 of 82 modules done
recompiling module csr_regfile
recompiling module perf_counters
recompiling module controller
recompiling package wt_cache_pkg
recompiling module wt_cache_subsystem
recompiling module cva6_icache
recompiling module wt_dcache_wbuffer
recompiling module wt_axi_adapter
recompiling module instr_tracer_if
recompiling module instr_tracer
recompiling package rvfi_pkg
recompiling module rvfi_tracer
recompiling module SimDTM
recompiling module lfsr_16bit
recompiling module tc_sram_wrapper
recompiling module addr_decode
recompiling module axi_demux
recompiling module axi_mux
recompiling module apb_uart
recompiling module rv_plic_target
recompiling package cvxif_instr_pkg
recompiling module cvxif_example_coprocessor
recompiling module instr_scan
recompiling module cvxif_fu
recompiling module cva6_tlb_sv32
recompiling module pmp
recompiling module wt_dcache_ctrl
recompiling module spill_register
recompiling module axi_demux_id_counters
recompiling module axi_id_prepend
recompiling module timer
recompiling module pmp_entry
All of 82 modules done
make[2]: Entering directory `/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/work-vcs/csrc'
make[2]: Leaving directory `/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/work-vcs/csrc'
make[2]: Entering directory `/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/work-vcs/csrc'
rm -f _cuarc*.so _csrc*.so pre_vcsobj_*.so share_vcsobj_*.so
g++ -w  -pipe -DVCSMX -DUVM_DPI_DO_TYPE_CHECK -fPIC -O -I/home/VCS2023/vcs/S-2021.09-SP2-7/include    -c /home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/dpi/uvm_dpi.cc
if [ -x ../simv ]; then chmod a-x ../simv; fi
g++  -o ../simv      -rdynamic -Wl,-E -Wl,-rpath='$ORIGIN'/simv.daidir -Wl,-rpath=./simv.daidir -Wl,-rpath='$ORIGIN'/simv.daidir/scsim.db.dir -Wl,-rpath=./simv.daidir/scsim.db.dir -Wl,-rpath=/home/VCS2023/vcs/S-2021.09-SP2-7/linux64/lib -L/home/VCS2023/vcs/S-2021.09-SP2-7/linux64/lib -Wl,-rpath-link=./ -Wl,--no-as-needed  /usr/lib64/libnuma.so.1 /home/VCS2023/vcs/S-2021.09-SP2-7/linux64/lib/vpdlogstub.o uvm_dpi.o   objs/amcQw_d.o   _24265_archive_1.so  SIM_l.o      rmapats_mop.o rmapats.o rmar.o rmar_nd.o  rmar_llvm_0_1.o rmar_llvm_0_0.o         libvhdlobjs.so vh/scscomm.o vh/scsFilelist.o   -lerrorinf -lsnpsmalloc -lvfs    -lvirsim -lvcsnew /home/VCS2023/vcs/S-2021.09-SP2-7//linux64/lib/vcs_main.o libvcsmx.so -lreader_common /home/VCS2023/vcs/S-2021.09-SP2-7/linux64/lib/libBA.a -lsimprofile -luclinative /home/VCS2023/vcs/S-2021.09-SP2-7/linux64/lib/vcs_tls.o   -Wl,-whole-archive      -Wl,-no-whole-archive        ./../simv.daidir/vc_hdrs.o    /home/VCS2023/vcs/S-2021.09-SP2-7/linux64/lib/vcs_save_restore_new.o -ldl  -lc -lm -lpthread -ldl 
../simv up to date
make[2]: Leaving directory `/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/work-vcs/csrc'
CPU time: 7.262 seconds to compile + .251 seconds to elab + .305 seconds to link
make[1]: Leaving directory `/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6'
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/work-vcs/simv  +permissive -sv_lib /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/work-dpi/ariane_dpi \
  +tohost_addr=80001000 \
  +PRELOAD=/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/cva6/sim/out_2023-03-23/directed_asm_tests/riscv_mstatus_csr_test_0.o +permissive-off ++/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/cva6/sim/out_2023-03-23/directed_asm_tests/riscv_mstatus_csr_test_0.o +debug_disable=1
Chronologic VCS simulator copyright 1991-2021
Contains Synopsys proprietary information.
Compiler version S-2021.09-SP2-7_Full64; Runtime version S-2021.09-SP2-7_Full64;  Mar 23 02:24 2023
UVM_INFO /home/VCS2023/vcs/S-2021.09-SP2-7//etc/uvm-1.2/base/uvm_root.svh(402) @ 0: reporter [UVM/RELNOTES] 
----------------------------------------------------------------
UVM-1.2.Synopsys
(C) 2007-2014 Mentor Graphics Corporation
(C) 2007-2014 Cadence Design Systems, Inc.
(C) 2006-2014 Synopsys, Inc.
(C) 2011-2013 Cypress Semiconductor Corp.
(C) 2013-2014 NVIDIA Corporation
----------------------------------------------------------------

  ***********       IMPORTANT RELEASE NOTES         ************

  You are using a version of the UVM library that has been compiled
  with `UVM_NO_DEPRECATED undefined.
  See http://www.eda.org/svdb/view.php?id=3313 for more details.

  You are using a version of the UVM library that has been compiled
  with `UVM_OBJECT_DO_NOT_NEED_CONSTRUCTOR undefined.
  See http://www.eda.org/svdb/view.php?id=3770 for more details.

      (Specify +UVM_NO_RELNOTES to turn off this notice)

### [rvfi_tracer] INFO: Using 'tohost' address 0x80001000

UVM_INFO /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_tb.sv(130) @ 0: reporter [Core Test] Preloading ELF: /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/cva6/sim/out_2023-03-23/directed_asm_tests/riscv_mstatus_csr_test_0.o
UVM_INFO /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_tb.sv(139) @ 10: reporter [Core Test] Loading Address: 0000000080000000, Length: 0000000000000374
UVM_INFO /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/ariane_tb.sv(139) @ 10: reporter [Core Test] Loading Address: 0000000080001000, Length: 0000000000000108
[TRACER] Output filename is: trace_hart_0.log
### [rvfi_tracer] INFO: Terminating on store of 0x00000003 into 'tohost' at PC 0x0000000080000170

$finish called from file "/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/core-v-cores/cva6/corev_apu/tb/rvfi_tracer.sv", line 85.
$finish at simulation time                10650
           V C S   S i m u l a t i o n   R e p o r t 
Time: 10650 ns
CPU Time:      0.220 seconds;       Data structure size:   5.2Mb
Thu Mar 23 02:24:55 2023
/home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/tools/spike//bin/spike-dasm --isa=rv32imc < ./trace_rvfi_hart_00.dasm > /home/t0268396/Desktop/CHAMSKI_TESTING/core-v-verif/cva6/sim/out_2023-03-23/vcs-testharness_sim/riscv_mstatus_csr_test_0.log
grep 0x0000000080000000 ./trace_rvfi_hart_00.dasm
core   0: 0x0000000080000000 (0xa5a5a637) DASM(a5a5a637)
3 0x0000000080000000 (0xa5a5a637) x12 0xa5a5a000
