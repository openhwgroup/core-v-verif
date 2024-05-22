# Generic Behavioural PLL

This model provides a behavioral model which can be inserted on a bus
to provide a random delay. The typical use case is when simulating
multi-cycle paths in an RTL simulation. 

A multi-cycle path is one where the delay is greater than one cycle, and
the timing constraints are relaxed to reflect this increased delay. In RTL
simulation, combinatorial logic updates in zero delay, and this multi-cycle
behaviour is not modeled correctly, which is dangerous. This model can
be inserted in the RTL, to insert a random delay that could be in a range.
In this way, if the design only works with a single cycle delay, it can
be found (with high, but not 100% confidence) during RTL simulation.

This module can be instantiated in the RTL of a
design, and the synthesized version (the code inside
of synopys tranlateon directives), will simply produce
a wire between the input and output ports. Thus the
resulting synthesized design is not modified.

In simulation, the model will insert a random delay between
the input bus or the output bus. This delay can either be
referenced to an absolute time values (specified in ps),
or it can be referenced to a number of clock cycles.  The
choice of this mode is based on a parameter CLOCK_BASED.

The range of the inserted delay is defined by two parameters
MIN_DELAY and MAX_DELAY. When in clock-based mode, these
parameters repesent a delay, expressed in units of 1/10th
of the clock period. A value of 10 corresponds to a delay
of one clock period, 20 corresponds two two clock periods,
5 corresponds to half a clock. When in absolute delay mode,
these parameters represent a minimum and maximum delay
expressed in pico-seconds.

Even in simulation, by default, no delay will be inserted.
To enable this feature the following +options may be used

```
+BEH_DELAY   == Must be present to cause the delays to be enabled.
```

```
+BEH_DELAY_DEBUG == If this is true, then messages will
                    printed by each instance, indicating
                    its mode of operation and the delays
                    it has selected (in FIXED_DELAY_MODE).
```

In all cases, a banner will be printed at time zero, stating
whether the BEH_DELAY is enabled - or not.

## Parameters

The following parameters can be used by the user

```
parameter integer BUS_WIDTH = 32
```
This paraemter controls the width of the bus. Note, all bits in the bus
are always delayed by the same amount.

```
parameter integer CLOCK_BASED = 1
```
This paraemter identifies whether the delays are specified in units of 
time-delay, or whether it is in units of clock cycles. Of course, if the
user choses to specify the delay in terms of clock cycles, then an input
clock must be provided on the clk port.

```
parameter integer MIN_DELAY = 10
parameter integer MAX_DELAY = 10
```

These parameters specify the lower and upper bound for the random delay.


```
parameter FIXED_DELAY MIN_DELAY = 1
```

This parameter specifies whether the delay is contnously randomized
during the simulation, or whether it is randomized only once at the
start of simulation.

## Integration

Typically this module would be inserted inside the RTL of a chip, in-line,
with a bus, for example on the read-data bus of a SRAM. The module is
coded such that it has synthesis pragmas. In synthesis it will appear
simply as a wire. To enable the delays, the user needs to include the
"+BEH_DELAY" on their simulation command line.

## Licensing
The beh_rand_delay is released under the Apache License, Version 2.0.
Please refer to the [LICENSE](LICENSE) file for further information.
