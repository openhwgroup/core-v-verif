# Reset Generator

## Introduction

The Reset Gererator is a SystemVerilog UVM module which is used to configure, generate and control a reset (one reset per reset_gen instance).

## Configuration

Users can configure the follwoing parameters:
```
	// -> p_init_value  = value when reset is not active
	
	// -> p_init_assert = number of clocks to assert reset
	
	// -> p_post_reset_delay = number of clocks after reset to terminate UVM reset phase
	
	// -> f_do_not_phase_jump = Flag to be set by user 
	//    If the flag is set, the reset driver is immune to the phase jump (it does nothing in the reset_phase after the phase jump
	
	// -> disable_auto_reset_phase = force the reset driver to ignore the reset phase
	//    It is then up to the user to manually assert and de-assert the reset using the procedural calls : manual_assert_reset() and manual_de_assert_reset().

	// -> assert_reset: Is an event to force reset 
```

## API

The class provides the following APIs.

```
	// ---------------------------------------------------------------------------------------------------------------------------
	// Using the flag disable_auto_reset_phase, we can force the reset driver to ignore the reset phase. It is then up to
	// the user to manually assert and de-assert the reset using the procedural calls: manual_assert_reset() and manual_de_assert_reset().
	// ---------------------------------------------------------------------------------------------------------------------------
	function void set_disable_auto_reset(bit disable_auto_reset_phase);
```

```
	// ----------------------------------------------------------------------------------
	// To manually assert the reset when using the flag disable_auto_reset_phase
	// ----------------------------------------------------------------------------------
	virtual task manual_assert_reset( );
```

```
	// ----------------------------------------------------------------------------------
	// To manually de-assert the reset when using the flag disable_auto_reset_phase
	// ----------------------------------------------------------------------------------
	virtual task manual_de_assert_reset( );
```

```

	// -----------------------------------------
	// API to force reset 
	// -----------------------------------------
	task emit_assert_reset();
```

```
	// ---------------------------------------------------------------------------------------------
	// API to set the number of reset a user wants to insert. It is used to manage on the fly reset
	// ---------------------------------------------------------------------------------------------
	function void set_num_reset(int N);
```

```
	// -----------------------------------------------------------------------------------------------
	// API to get the current number of reset already inserted. It is used to manage on the fly reset
	// -----------------------------------------------------------------------------------------------
	function int get_num_reset();
```

```
	// ---------------------------------------------------------
	// API to tell a user, all reset(== num_reset) are inserted 
	// ---------------------------------------------------------
	function bit get_reset_on_the_fly_done();
	// Example from the test: 
	// connect phase: Set the number of reset to be asserted  
	//	env.reset_driver.set_num_reset(6);
	// main phase:
	//	--> Set the criteria to insert the reset, in this example number of transaction is used
	//	--> Assert an reset every nb_trans 
	//	nb_trans = $urandom_range(20, 60);
	//     //------------------------
	//     //Assert reset  
	//     //------------------------
	//     fork 
	//		phase.raise_objection(this, "Start reset asertion");
	//		forever begin
	//	
	//			vif.wait_n_clocks(1); 
	//			if(env.reset_driver.get_reset_on_the_fly_done == 1) begin
	//	
	//				`uvm_info("RESET ON THE FLY END", $sformatf("%0d(d), %0d(d)",env.scoreboard.get_req_counter, nb_trans ), UVM_DEBUG);    
	//				phase.drop_objection(this, "Finish reset assertion");
	//				break;
	//	
	//			end
	//
	//			`uvm_info("RESET ON THE FLY", $sformatf("%0d(d), %0d(d)",env.scoreboard.get_req_counter, nb_trans ), UVM_DEBUG);
	//	
	//			if(env.scoreboard.get_req_counter() == nb_trans) begin
	//
	//				phase.drop_objection(this, "Assert reset");
	//				env.reset_driver.emit_assert_reset();
	//
	//			end
	//		end
	//	join_none
	//              
```


## Integration guide

Here is an example of a TB which required one reset, RESETN_A (value when reset is not active=1, number of clocks to assert reset=150, number of clocks after reset to terminate UVM reset phase=0)

### 1. In the top ENV: Instantiate and create clock driver
```
	import reset_driver_pkg::*;
	reset_driver_c #(1'b1,150,0)	reset_driver_RESETN_A;
```

#### Build phase	
```
	reset_driver_RESETN_A = reset_driver_c#( 1'b1,100,0 )::type_id::create("RESETN_A_top_reset_driver", this );
```

### 2. In the TestBench Top
```
	import reset_driver_pkg::*;
	
	bit		reset;
	wire logic	clk; // Either provided by the user or generated with the dv_utils Clock Generator
	wire logic	rst_n_A;
	bit		post_shutdown_phase;	
	
	xrtl_reset_vif #(1'b1,100,0) reset_if_A (.clk(clk),
						.reset(reset),
    						.reset_n(rst_n_A),                                       
    						.post_shutdown_phase(post_shutdown_phase));
   
   
	initial begin
		$timeformat(-9,0," ns", 7);
		uvm_config_db #( virtual xrtl_reset_vif #( 1'b1,100,0) )::set(uvm_root::get(), "*", "RESETN_A_top_reset_driver", reset_if_A );
		run_test();
	end  
```

## Licensing
The reset_gen is released under the Apache License, Version 2.0.
Please refer to the [LICENSE](LICENSE) file for further information.
