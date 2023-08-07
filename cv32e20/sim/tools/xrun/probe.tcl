set wavefile  waves.shm
database -open $wavefile -shm

probe -create -shm uvmt_cv32e20_tb.dut_wrap -all -depth all -shm -database $wavefile
run 
exit
