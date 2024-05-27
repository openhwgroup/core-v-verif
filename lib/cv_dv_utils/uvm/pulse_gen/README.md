# Pulse Generator

## Introduction

The Pulse Gererator is a SystemVerilog UVM module which is used to configure and generate pulses. Pulse Generator can be configured to generate multiple pulses. 
A pulse can be a sysncronous pulse with respect to a clock or an asynchronous pulse. Timeunit of pico second is used to genarate an asynchronous pulse. 

## Configuration

Here are the parameters that user should configure
```
    //////////////////////////////////////////////////////
    // generate a pulse only if m_enable = 1 
    /////////////////////////////////////////////////////
    rand bit unsigned                m_pulse_enable;
    
    //////////////////////////////////////////////////////
    // if 1: Generate a pulse synchronous to a clock
    //    0: Generate an asynchronos pulse  
    /////////////////////////////////////////////////////
    rand bit unsigned                m_pulse_clock_based;

    //////////////////////////////////////////////////////
    // if m_pulse_clock_based: 1:  the time in clock cycle between 2 pulses 
    // if m_pulse_clock_based: 0:  the time in ps between 2 pulses 
    /////////////////////////////////////////////////////
    rand int unsigned                m_pulse_period;

    //////////////////////////////////////////////////////
    // total number of pulses 
    /////////////////////////////////////////////////////
    rand int unsigned                m_pulse_num;

    //////////////////////////////////////////////////////
    // if m_pulse_clock_based: 1:  width of a pulse in clock cycles 
    // if m_pulse_clock_based: 0:  width of a pulse in ps 
    /////////////////////////////////////////////////////
    rand int unsigned                m_pulse_width; 

    //////////////////////////////////////////////////////
    // if m_pulse_clock_based: 1:  phase shift of a pulse with respect to a clock in %
    // --> ex: 25 -> 25*clock_period/100 ps of delay after posedge of a clock 
    // --> first cycle after reset is used to calculate the clock frequency 
    //
    // if m_pulse_clock_based: 0:  not used 
    /////////////////////////////////////////////////////
    rand int unsigned                m_pulse_phase_shift; 
```
## APIs 

Pulse driver provides following APIs. 
```
    // APIs to configure pulse generator
    // to enable or disable pulse generator
    function void set_pulse_enable (int unsigned enable);

    // to set synchronous or asynchoronous pulse generation
    function void set_pulse_clock_based (int unsigned clock_based);

    // to set number of pulse to be generated 
    function void set_pulse_num (int unsigned num);

    // to set pulse width to be generated 
    function void set_pulse_width (int unsigned width);

    // to set pulse period 
    function void set_pulse_period (int unsigned period);

    // to set pulse phase shift with respect to a clock
    // 25 -> 25%clock_period 
    function void set_pulse_phase_shift (int unsigned phase_shift);

    // ------------------------------------------------------------------------
    // Convert2String
    //
    // Return configuration in a pretty, one-line format
    // ------------------------------------------------------------------------
    virtual function string convert2string();

```

## Integration guide
Following is an example of a TB where a pulse generator is instantiated. It shall generate 10 synchronous pulses of 1 clock cycle with a phase shift of 25%. 
The pulses are generated every 1000 clock cycles. 


### 1. In the top ENV: Instantiate and create pulse driver and pulse configuration class. 

```
  import pulse_gen_pkg::*;

  pulse_gen_driver             m_pulse_driver; 
  pulse_gen_cfg                m_pulse_cfg; 
```

#### Build phase	

```
    m_pulse_driver         = pulse_gen_driver::type_id::create("pulse_driver", this );
    m_pulse_cfg            = pulse_gen_cfg::type_id::create("pulse_cfg", this );

```
#### Connect phase

```
    m_pulse_driver.m_pulse_cfg      = m_pulse_cfg;
```

#### End of elaboration phase (often in testbase)	

```
    // -----------------------------------
    // Configure pulse generator
    // -----------------------------------
    env.m_pulse_cfg.set_pulse_enable(1);

    // synchronous pulse 
    env.m_pulse_cfg.set_pulse_clock_based(1);

    // of 1 clock cycle 
    env.m_pulse_cfg.set_pulse_width(1);

    // generated every 1000 clock cycles 
    env.m_pulse_cfg.set_pulse_period(1000);

    // with a phase shift by 25%
    env.m_pulse_cfg.set_pulse_phase_shift(25);

    // 10 such pulses are generated 
    env.m_pulse_cfg.set_pulse_num(10);

    `uvm_info("TEST BASE", $sformatf("PULSE CONFIGURATION %s", env.m_pulse_cfg.convert2string()), UVM_LOW)

```

### 2. In the TestBench Top

```
    import pulse_gen_pkg::*;
    
    // interface thats gives a pulse 
    pulse_if                    pulse_vif (.clk(clk), .rstn(rst_n));

    assign pulse = pulse_vif.m_pulse_out; 
    
	initial begin
		uvm_config_db #( virtual pulse_if)::set(uvm_root::get() , "*" , "pulse_driver" , pulse_vif);
	end  
```

## Licensing
The pulse_gen is released under the Apache License, Version 2.0.
Please refer to the [LICENSE](LICENSE) file for further information.
