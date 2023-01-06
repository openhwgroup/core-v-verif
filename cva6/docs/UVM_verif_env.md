<!-- Output copied to clipboard! -->

<!-----

You have some errors, warnings, or alerts. If you are using reckless mode, turn it off to see inline alerts.
* ERRORs: 0
* WARNINGs: 0
* ALERTS: 1

Conversion time: 0.661 seconds.

Using this Markdown file:

1. Paste this output into your source file.
2. See the notes and action items below regarding this conversion run.
3. Check the rendered output (headings, lists, code blocks, tables) for proper
   formatting and use a linkchecker before you publish this page.

Conversion notes:

* Docs to Markdown version 1.0β34
* Thu Jan 05 2023 06:35:32 GMT-0800 (PST)
* Source doc: Verif_env Documentation CV6 
* Tables are currently converted to HTML tables.
* This document has images: check for >>>>>  gd2md-html alert:  inline image link in generated source and store images to your server. NOTE: Images in exported zip file from Google Docs may not appear in  the same order as they do in your doc. Please check the images!

----->



# The CV6 UVM Verification Environment

This document describes the uvm verification environment of the cv6 core. This environment is intended to be able to verify the cv6 core and run different test cases by the minimal modification to the environment itself.  The environment is shown below:


![alt_text](../images/1.png "image_tooltip")

***

This environment consist of the following

1. Simple two uvm agents for the clock_reset and cvxif interfaces.
2. Result checking capability is built into the environment so the test cases do not need to determine and check for the pass/fail criteria.

The environment consists of disjoint components. When a user invokes a command to run a test case a set of scripts and makefile rules are invoked to compile the environment and tests, run the simulation and check the results. On running a particular test it generates a .bin file which then is loaded into the main memory in the tb_top at the Boot_address of the core and the instructions are then start executing.
 

## Clock and reset agent

This agent is responsible for the clock generation and reset assert and deassert.It uses a typical sequencer for the arbitration of the sequences. There are two main sequences in this agent that we will run: the start clock sequence and the stop clock sequence.

### Clk_rst_interface

Clk_rst_Interface is used for the clock generation and setting the clock period. This interface consists of the following signals.

<table>
  <tr>
   <td><strong>signal</strong>
   </td>
   <td><strong>Description</strong>
   </td>
  </tr>
  <tr>
   <td>clock
   </td>
   <td>Controls the Clock fed to the design under test.
   </td>
  </tr>
  <tr>
   <td>reset
   </td>
   <td>Control the reset state of the design under test.
   </td>
  </tr>
</table>

### UVM_objects
There are two uvm_objects that are cfg and cntxt.

### Sequence_item

 It randomizes the deassert period of the reset and clock period. It randomizes the operations that we want to perorm and the initial values.

### Sequence

 It consists of two main sequences: start clock,stop clock that are extended from the base sequence and it sends operations that we want to perform with the clock and reset.

### Driver

Driver has a drv_req task that drives the reset and clock signal depending upon the current sequence_item received. And then call the write method for the analysis port to send the sequence_item to the coverage model.

### Monitor

This is a simple uvm_component.It monitors reset and clock if the configuration enable signal is high and then broadcasts the sequence_item  to the coverage model.

### Coverage Model

This is the uvm_component class that collects the coverage once  configuration enable and cov_model enable signal is high. It gets the sent sequence_item from the monitor and driver and collects the coverage.

### Clk_rst_agent

Clk_rst_agent  is an active agent which continuously monitors and drives clock and reset from the design under test(DUT). It gets the configuration object up from the testbench hierarchy and sets them for the components within the agent. clk_rst agent can also collect coverage if the cov_model enable signal is high. It connects components within the agent.


## Cvxif Agent

Cv-xif agent supports custom instructions. Upon receiving the issue request it drives the response one clock cycle after the issue request.

### Cvxif interface:

The interface consist of the two enum variables.

<table>
  <tr>
   <td><strong>Enum Variable</strong>
   </td>
   <td><strong>Description</strong>
   </td>
  </tr>
  <tr>
   <td>Cvxif_req_i
   </td>
   <td>The request is send to get a response
   </td>
  </tr>
  <tr>
   <td>Cvxif_resp_o
   </td>
   <td>The response is generated according to the request.
   </td>
  </tr>
</table>

### UVM_objects
There are two uvm_objects that are cfg and cntxt.

### Sequence_item

Cvxif agent has two sequence items one req_sequence_item and resp_sequence_item.

### Sequencer

Cvxif sequencer component is typical and it contains a FIFO which get the req_item from the monitor.

### Sequence

The req_sequence_item is received from the sequencer using the p_sequencer handle. Instruction received is then checked whether it is illegal/legal and then we do two things: if the instruction received through the req_item is legal we send the response using the `uvm_send macro otherwise we send a default response.

### Driver
In the driver using get_next_item we get the resp_item. Then we drive the resp_sequence_item on to the interface at posedge of the clock.


### Monitor

Monitor of the cvxif agent gets the signal from the interface and assigns them to the req_item and resp_item and publishes them. Req_item is published to the sequencer and the cov_model using the analysis port write method. On the other hand resp_item is published to the cov_model only.


### Cov_model 

The coverage model collects coverage based on the configuration enable and cov_model enabled signal for the resp_item and the req_item.


### Cvxif Agent

This class extends uvm_agent.In this class we get the configuration objects that are set at the top hierarchy in the testbench we connect and create the components of the agent.  We set the configuration objects for the components down in the hierarchy.


## Cv6 environment

This class extends from the uvm_environment. In this class we create our agents and connect the monitor req analysis port of the cvxif agent with the coverage model in the environment. We get the configuration objects that are set in the hierarchy above and set them for the hierarchy down. We start the cvxif_seq using the start method in the run_phase of the environment.

### UVM_objects
There are two uvm_objects that are cfg and cntxt. The cfg object set the constaraints for the agent objects. We set the values of cfg and cntxt using configuration database set method for the agents. Also we randomizes the agents objects as well.

### Virtual sequencer
 This class extends from uvm_sequencer and has the handles of both the agent sequencers.

### Virtual sequence

 This sequence is responsible for the starting of the clock and giving the initial reset pulse to the design under test. The virtual sequence sends the sequence item to the clk_rst_ sequencer. First it sets the action to the start_clk and then to assert reset.

## Cv6 test
 In the test class we start the virtual sequence by raising an objection once the virtual sequece is done with its execution it drops the objection and the simulation is finished. 


## CV6 tb_top
In this module we instantiates the interfaces and the cv6. We set the interfaces for the agents using the configuration database set method. In this module we check the error count and fatal count and sim_finished and print the result of the simulation.

