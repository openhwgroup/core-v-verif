onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /beh_rand_delay_unit_tb/clk1
add wave -noupdate /beh_rand_delay_unit_tb/clk2
add wave -noupdate /beh_rand_delay_unit_tb/bus_in1
add wave -noupdate /beh_rand_delay_unit_tb/bus_out1
add wave -noupdate /beh_rand_delay_unit_tb/bus_in2
add wave -noupdate /beh_rand_delay_unit_tb/bus_out2
add wave -noupdate /beh_rand_delay_unit_tb/bus_in3
add wave -noupdate /beh_rand_delay_unit_tb/bus_out3
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/DUT1/bus_in
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/DUT1/bus_out
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/bus1_in_count
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/bus1_out_count
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/DUT1/clk
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/DUT1/delay_is_enabled
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/DUT1/debug_enabled
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/DUT1/delayed_bus
add wave -noupdate -expand -group DUT1 -radix unsigned /beh_rand_delay_unit_tb/DUT1/last_clock_edge_ps
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/DUT1/last_clock_edge_valid
add wave -noupdate -expand -group DUT1 -radix unsigned /beh_rand_delay_unit_tb/DUT1/clock_period_ps
add wave -noupdate -expand -group DUT1 -radix unsigned /beh_rand_delay_unit_tb/DUT1/new_clock_period_ps
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/DUT1/clock_period_valid
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/DUT1/clock_period_changed
add wave -noupdate -expand -group DUT1 -radix unsigned /beh_rand_delay_unit_tb/DUT1/current_delay_ps
add wave -noupdate -expand -group DUT1 -radix unsigned /beh_rand_delay_unit_tb/DUT1/last_input_trans_time_ps
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/DUT1/current_delay_valid
add wave -noupdate -expand -group DUT2 /beh_rand_delay_unit_tb/DUT2/bus_in
add wave -noupdate -expand -group DUT2 /beh_rand_delay_unit_tb/DUT2/bus_out
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/bus2_in_count
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/bus2_out_count
add wave -noupdate -expand -group DUT2 /beh_rand_delay_unit_tb/DUT2/clk
add wave -noupdate -expand -group DUT2 /beh_rand_delay_unit_tb/DUT2/delay_is_enabled
add wave -noupdate -expand -group DUT2 /beh_rand_delay_unit_tb/DUT2/debug_enabled
add wave -noupdate -expand -group DUT2 /beh_rand_delay_unit_tb/DUT2/delayed_bus
add wave -noupdate -expand -group DUT2 -radix unsigned /beh_rand_delay_unit_tb/DUT2/last_clock_edge_ps
add wave -noupdate -expand -group DUT2 /beh_rand_delay_unit_tb/DUT2/last_clock_edge_valid
add wave -noupdate -expand -group DUT2 -radix unsigned /beh_rand_delay_unit_tb/DUT2/clock_period_ps
add wave -noupdate -expand -group DUT2 -radix unsigned /beh_rand_delay_unit_tb/DUT2/new_clock_period_ps
add wave -noupdate -expand -group DUT2 /beh_rand_delay_unit_tb/DUT2/clock_period_valid
add wave -noupdate -expand -group DUT2 /beh_rand_delay_unit_tb/DUT2/clock_period_changed
add wave -noupdate -expand -group DUT2 -radix unsigned /beh_rand_delay_unit_tb/DUT2/current_delay_ps
add wave -noupdate -expand -group DUT2 -radix unsigned /beh_rand_delay_unit_tb/DUT2/last_input_trans_time_ps
add wave -noupdate -expand -group DUT2 /beh_rand_delay_unit_tb/DUT2/current_delay_valid
add wave -noupdate -expand -group DUT3 /beh_rand_delay_unit_tb/DUT3/bus_in
add wave -noupdate -expand -group DUT3 /beh_rand_delay_unit_tb/DUT3/bus_out
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/bus3_in_count
add wave -noupdate -expand -group DUT1 /beh_rand_delay_unit_tb/bus3_out_count
add wave -noupdate -expand -group DUT3 /beh_rand_delay_unit_tb/DUT3/clk
add wave -noupdate -expand -group DUT3 /beh_rand_delay_unit_tb/DUT3/delay_is_enabled
add wave -noupdate -expand -group DUT3 /beh_rand_delay_unit_tb/DUT3/debug_enabled
add wave -noupdate -expand -group DUT3 /beh_rand_delay_unit_tb/DUT3/delayed_bus
add wave -noupdate -expand -group DUT3 -radix unsigned /beh_rand_delay_unit_tb/DUT3/last_clock_edge_ps
add wave -noupdate -expand -group DUT3 /beh_rand_delay_unit_tb/DUT3/last_clock_edge_valid
add wave -noupdate -expand -group DUT3 -radix unsigned /beh_rand_delay_unit_tb/DUT3/clock_period_ps
add wave -noupdate -expand -group DUT3 /beh_rand_delay_unit_tb/DUT3/new_clock_period_ps
add wave -noupdate -expand -group DUT3 /beh_rand_delay_unit_tb/DUT3/clock_period_valid
add wave -noupdate -expand -group DUT3 /beh_rand_delay_unit_tb/DUT3/clock_period_changed
add wave -noupdate -expand -group DUT3 -radix unsigned /beh_rand_delay_unit_tb/DUT3/current_delay_ps
add wave -noupdate -expand -group DUT3 -radix unsigned /beh_rand_delay_unit_tb/DUT3/last_input_trans_time_ps
add wave -noupdate -expand -group DUT3 /beh_rand_delay_unit_tb/DUT3/current_delay_valid
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
quietly wave cursor active 0
configure wave -namecolwidth 342
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
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
WaveRestoreZoom {0 ps} {881 ps}
