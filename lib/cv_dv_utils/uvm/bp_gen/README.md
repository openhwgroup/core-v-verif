# Back Pressure Generator

## Introduction

The Back Pressure (BP) Gererator is a SystemVerilog UVM module which can generate back-pressure.
The bp_gen package provides a virtual sequencer that user can use to be able to choses between one of the four sequences provided (see sequence's part hereafter).

## Configuration

Users can either use one of the existing sequences (see in the next part below) or create their own sequence to configure the BP type() (OFF or ON, the duration cycle and the percentage (or frequency rate))

```
	typedef enum {	BP_OFF=0,      // BP OFF - for N, number of indicated clocks
			        BP_ON=1,       // BP ON  - for N, number of indicated clocks,
               		BP_TOGGLE=2,   // BP toggles every Mth cycles for N clocks
               		BP_PERCENT=3 } // BP is asserted M% of the time for N clocks
					bp_drive_type_t;


	// -------------------------------------------------------------------------
	// Random Fields for the BP transaction
	// -------------------------------------------------------------------------
	rand bp_drive_type_t	m_bp_type;
	rand int		        m_N;   // duration
	rand int		        m_M;   // either percent or toggle freq

```

If user uses the virtual sequence provided with the bp_gen, s(h)e should configure following fields (see example in the section "integration guide")  
```
    typedef enum {
        NO_BP, // selects no_bp_sequence
        HEAVY_BP, // selects heavy_bp_sequence 
        OCCASSIONAL_BP, // selects occassional_bp_sequence 
        MOSTLY_BP // selects mostly_bp sequence 
    } bp_type_t;

    // In the virtual sequence following fields need to be passe 

    // Type of the back pressure to be applied
    bp_type_t    which_bp;
    /// Target Agent Sequencers
    bp_sequencer bp_sqr;

```

## APIs 
The virtual sequence provides following APIs to set bp_type and sequencer 
```
 function void set_bp_type(bp_type_t bp);
 function void set_bp_sequencer(bp_sequencer sqr);
```

## Sequence

Sequence where bp type is always at BP_OFF
```	
	no_bp_sequence
```

Sequence where bp type is BP_OFF at 80% and BP_ON at 20%
```
	occassional_bp_sequence
```

Sequence where bp type is BP_OFF at 80% and BP_ON at 20%
```
	heavy_bp_sequence
```

Sequence where bp type is BP_OFF around 10% and BP_ON around 90%
```
	mostly_bp_sequence
```

## Integration guide
This guide is based on the example of a AXI interface


### 1. In the top ENV: Instantiate and create clock driver

```
	import bp_driver_pkg::*;
	
	bp_agent              aw_bp_agent ;
	bp_agent              w_bp_agent  ;
	bp_agent              b_bp_agent  ;
	bp_agent              ar_bp_agent ;
	bp_agent              r_bp_agent  ;

	bp_virtual_sequence   aw_bp_vseq ;
	bp_virtual_sequence   w_bp_vseq  ;
	bp_virtual_sequence   b_bp_vseq  ;
	bp_virtual_sequence   ar_bp_vseq ;
	bp_virtual_sequence   r_bp_vseq  ;

```

#### Build phase

```
	aw_bp_agent = bp_agent::type_id::create( "aw_bp_agent" , this );
	w_bp_agent  = bp_agent::type_id::create( "w_bp_agent"  , this );
	b_bp_agent  = bp_agent::type_id::create( "b_bp_agent"  , this );
	ar_bp_agent = bp_agent::type_id::create( "ar_bp_agent" , this );
	r_bp_agent  = bp_agent::type_id::create( "r_bp_agent"  , this );

	aw_bp_vseq = bp_virtual_sequence::type_id::create( "aw_bp_sequence" , this);
	w_bp_vseq  = bp_virtual_sequence::type_id::create( "w_bp_sequence"  , this);
	b_bp_vseq  = bp_virtual_sequence::type_id::create( "b_bp_sequence"  , this);
	ar_bp_vseq = bp_virtual_sequence::type_id::create( "ar_bp_sequence" , this);
	r_bp_vseq  = bp_virtual_sequence::type_id::create( "r_bp_sequence"  , this);
```

#### Connect phase

```
	// Sequencer to virtual sequence 
	aw_bp_vseq.set_bp_sequencer(aw_bp_agent.m_sequencer);
	w_bp_vseq.set_bp_sequencer(w_bp_agent.m_sequencer ) ;
	b_bp_vseq.set_bp_sequencer(b_bp_agent.m_sequencer ) ;
	ar_bp_vseq.set_bp_sequencer(ar_bp_agent.m_sequencer);
	r_bp_vseq.set_bp_sequencer(r_bp_agent.m_sequencer ) ;

	// BP type to virtuals sequence 
	aw_bp_vseq.set_bp_type(aw_bp_cfg.m_bp_type) ;
	w_bp_vseq.set_bp_type(w_bp_cfg.m_bp_type)   ;
	b_bp_vseq.set_bp_type(b_bp_cfg.m_bp_type)   ;
	ar_bp_vseq.set_bp_type(ar_bp_cfg.m_bp_type) ;
	r_bp_vseq.set_bp_type(r_bp_cfg.m_bp_type)   ;
```

### 2. In the TestBench Top

```
	import bp_driver_pkg::*;
	
	bp_vif #(1) aw_bp   ( .clk( clk_i ), .rstn( reset_n ) );
	bp_vif #(1) w_bp    ( .clk( clk_i ), .rstn( reset_n ) );
	bp_vif #(1) b_bp    ( .clk( clk_i ), .rstn( reset_n ) );
	bp_vif #(1) ar_bp   ( .clk( clk_i ), .rstn( reset_n ) );
	bp_vif #(1) r_bp    ( .clk( clk_i ), .rstn( reset_n ) );
```

``` 
	assign axi_vif.aw_ready = ~aw_bp.bp_out ;
	assign axi_vif.w_ready  = ~w_bp.bp_out  ;
	assign axi_vif.b_ready  = ~b_bp.bp_out  ;
	assign axi_vif.ar_ready = ~ar_bp.bp_out ;
	assign axi_vif.r_ready  = ~r_bp.bp_out  ;
```

```
	initial begin      
		uvm_config_db #(virtual bp_vif #(1) )::set(uvm_root::get(), "*", "aw_bp_agent" , aw_bp ) ;
		uvm_config_db #(virtual bp_vif #(1) )::set(uvm_root::get(), "*", "w_bp_agent"  , w_bp  ) ;
		uvm_config_db #(virtual bp_vif #(1) )::set(uvm_root::get(), "*", "b_bp_agent"  , b_bp  ) ;
		uvm_config_db #(virtual bp_vif #(1) )::set(uvm_root::get(), "*", "ar_bp_agent" , ar_bp ) ;
		uvm_config_db #(virtual bp_vif #(1) )::set(uvm_root::get(), "*", "r_bp_agent"  , r_bp  ) ;
      
		run_test();
	end
```

## Licensing
The bp_gen is released under the Apache License, Version 2.0.
Please refer to the [LICENSE](LICENSE) file for further information.
