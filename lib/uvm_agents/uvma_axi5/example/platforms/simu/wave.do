onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /top/ivif/clk
add wave -noupdate /top/ivif/rst_n
add wave -noupdate /top/ivif/cf
add wave -noupdate /top/ivif/data_in0
add wave -noupdate /top/ivif/data_in1
add wave -noupdate /top/ovif/data_out0
add wave -noupdate /top/ovif/data_out1
add wave -noupdate /top/ivif/enable
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {15225 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 335
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ns} {10000 ns}
run -all
