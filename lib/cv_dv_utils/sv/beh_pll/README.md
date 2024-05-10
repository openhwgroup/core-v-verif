# Generic Behavioural PLL

A PLL is a complex IP, that is typically purchased from a specialized
IP provider. Sometimes, early in a project, the actual PLL is not yet
available, and it can be helpful to have a behavioural model of a PLL.

This is a behavioural model of a PLL which takes in a reference clock.
The model has two ports (multiply/divide) which are real numbers and the
PLL outputs an output clock whose frequency is equal to the frequency
of the input clock multiplied by the multiply and divided by divide.
Of course, it is uncommon to use real values in actual designs, so
typically the user would provide a wrapper which converts the outputs
of their CSRs with these values, to real values. In this way, this
model can cover the case of a fractional PLL.

The model also has a fake locked signal which is raised a random time
between default_min_time_to_lock_ps and default_max_time_to_lock_ps,
which are both parameters the user can set.

## Integration

During the early phase of a SoC design, if an actual vendor PLL model
is not available, this behaviour model can be used temporarily as
a place-holder. Either this module can be directly instantiated in
the RTL, or the user might choose to place this model in a wrapper
so that the connections are aligned with those of a vendor PLL.

## Licensing
The beh_pll is released under the Apache License, Version 2.0.
Please refer to the [LICENSE](LICENSE) file for further information.
