# Watchdog

## Introduction

The Watchdog is a SystemVerilog UVM module which provides a global watchdog timer that terminates the simulation once a maximum delay is reached.


## Configuration

The maximum delay can be set by a plusarg (+TIMEOUT=xxx) specified in ns. On timeout, a list of the objectors is provided (List the class / object which have an objection raised).

## Integration guide

Here is the example of a TB into which user want to have a watchdog managing a timeout after 10ms


### 1. In the top ENV
```
	import watchdog_pkg::*;
	
	watchdog_c      m_wd;
```
#### Build phase
```
	m_wd = watchdog_c::type_id::create("m_wd",this);
```

### 2. In the simulation command
User sets the plusarg TIMEOUT to 100000

## Licensing
The watchdog is released under the Apache License, Version 2.0.
Please refer to the [LICENSE](LICENSE) file for further information.
