# Back Pressure Generator

## Introduction

The Back Pressure (BP) Gererator is a SystemVerilog UVM module which can generate back-pressure.
It is important to note that virtual sequencer / sequences are not provided with the bp_gen package. It is up to the user to implement his/her own virtual sequencer / sequences to be able to chose between one of the four sequences provided (see sequence's part hereafter)

## Configuration

Users can either use one the existing sequences (see in the next part below) or create their own sequence to configure the BP type() (OFF or ON, the duration cycle and the percentage (or frequency rate))

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
	aw_bp_vseq.bp_sqr = aw_bp_agent.m_sequencer ;
	w_bp_vseq.bp_sqr  = w_bp_agent.m_sequencer  ;
	b_bp_vseq.bp_sqr  = b_bp_agent.m_sequencer  ;
	ar_bp_vseq.bp_sqr = ar_bp_agent.m_sequencer ;
	r_bp_vseq.bp_sqr  = r_bp_agent.m_sequencer  ;
```

### 2. In the TestBench Top

```
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
