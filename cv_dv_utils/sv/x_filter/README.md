## X Filter

### Description

This is a behavioural model that can be used to filter
Xs or Zs out of a bus. Great care should be used when using
this model, as it can easily mask real bugs. 

Two instantiation parameters (filter_x, filter_z) can be
used to control whether only x, only z or both values
are filter. 

By default, x's or z's are replaced with random values.
However, this can be modified by
the instantiation parameter (filter_to) to select
a zero or one as the new value.

The x-masking filter can be globally disabled using
a +option at start of simulation.

### Plus Arg Options

````
+NO_X_FILTER   == Disable all X or Z filtering.
````

````
+X_FILTER_DEBUG == If this is true, then messages will printed each time 
                   an x or value is replaced.
````

In all cases, a banner will be printed at time zero, stating whether the
BEH_DELAY is enabled - or not.

## Parameters

The following verilog parameters can be set by the user:

---
| Parameter | Description |
---

## Integration

## Licensing
The x_filter is released under the Apache License, Version 2.0.
Please refer to the [LICENSE](LICENSE) file for further information.
