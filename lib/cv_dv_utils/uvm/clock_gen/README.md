# Clock Generator

## Introduction

The Clock Gererator is a SystemVerilog UVM module which is used to configure, generate and control a clock (one clock per clock_gen instance).

## Configuration

User can configure the clock frequency, duty cycle and starting signal level. They can also control the start and the stop of a clock.

Here are the three parameters which can be configured
```
    //////////////////////////////////////////////////////
    //Configuration Parameters
    //To be driven by the driver 
    /////////////////////////////////////////////////////
    rand  bit m_starting_signal_level;
    rand  int m_clock_frequency = 10;   // safe default value (10Mhz) in case no randomization is done
    rand  int m_duty_cycle = 50;        // safe default value (50%) in case no randomization is done
```
## APIs 

Clock driver provides following APIs. 
```
   //-----------------------------------------------------------
   // Global Clock Counter
   // User should use this task to start a global clock counter 
   //----------------------------------------------------------
   task global_cycle_counter();
   //------------------------------------------------------------------------
   // If user has started the task global clock counter 
   // --> Following API can be used to get the value of global clock counter
   //------------------------------------------------------------------------
   function int get_global_cycle_counter();
   //---------------------------------------------
   // Task to start the clock from the uvm class  
   //--------------------------------------------
   virtual task start_clock();
   //---------------------------------------------
   // Task to stop the clock from the uvm class
   //--------------------------------------------
   virtual task stop_clock();
```

## Integration guide
Following is an example of a TB which requirs two clocks, CLK_A (freq=20Mhz,duty_cycle=50%,starting_signal_level=1) and CLK_B (freq=15Mhz,duty_cycle=60%,starting_signal_level=0)

### 1. In the top ENV: Instantiate and create clock driver and clock configuration class. 

```
	import clock_driver_pkg::*;
	
	clock_driver_c			clock_driver_CLK_A;
	clock_config_c			clock_cfg_CLK_A;

	clock_driver_c			clock_driver_CLK_B;
	clock_config_c			clock_cfg_CLK_B;
```

#### Build phase	

```
	clock_driver_CLK_A = clock_driver_c::type_id::create("clock_driver_CLK_A", this );
	clock_cfg_CLK_A    = clock_config_c::type_id::create("clock_cfg_CLK_A", this );
	clock_driver_CLK_A.m_clk_cfg = clock_cfg_CLK_A;
    
	clock_driver_CLK_B = clock_driver_c::type_id::create("clock_driver_CLK_B", this );
	clock_cfg_CLK_B    = clock_config_c::type_id::create("clock_cfg_CLK_B", this );
	clock_driver_CLK_B.m_clk_cfg = clock_cfg_CLK_B;
```

#### En of elaboration phase	

```
	if (!clock_cfg_CLK_A.randomize() with {m_starting_signal_level == 1; m_clock_frequency == 20; m_duty_cycle == 50;}) begin
		`uvm_error("End of elaboration", "Randomization failed");
	end

	if (!clock_cfg_CLK_B.randomize() with {m_starting_signal_level == 0; m_clock_frequency == 15; m_duty_cycle == 60;}) begin
		`uvm_error("End of elaboration", "Randomization failed");
	end
```

### 2. In the TestBench Top

```
	import clock_driver_pkg::*;
	
	wire logic	clk_A;
	wire logic	clk_B;
	
	xrtl_clock_vif clock_if_CLK_A( .clock(clk_A));
	xrtl_clock_vif clock_if_CLK_B( .clock(clk_B));	
	

	initial begin
		$timeformat(-9,0," ns", 7);
		uvm_config_db #( virtual xrtl_clock_vif)::set(uvm_root::get() , "*" , "clock_driver_CLK_A" , clock_if_CLK_A);
		uvm_config_db #( virtual xrtl_clock_vif)::set(uvm_root::get() , "*" , "clock_driver_CLK_B" , clock_if_CLK_B);
		run_test();
	end  
```

## Licensing
The clock_gen is released under the Apache License, Version 2.0.
Please refer to the [LICENSE](LICENSE) file for further information.
