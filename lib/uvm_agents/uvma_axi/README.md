# AXI (Advanced eXtensible Interface)  UVM Agent
This IP contains the AXI (Advanced eXtensible Interface) UVM Agent.


- The agent is developed referring to the Spec in the link below:
    https://developer.arm.com/documentation/ihi0022/hc


- Passive agent: the axi agent acts by default as a passive agent; in
  configuration object we have  ``is_active == UVM_PASSIVE``.


- Active slave agent: the active mode is not yet supported by the axi
  agent. The uvma_axi_mem component shall be completed to act as a
  memory for the slave agent. Also, the connection of the memory ports
  with monitor ports shall be done in uvma_axi_agent.
