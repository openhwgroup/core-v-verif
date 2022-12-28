
/*

This support logic submodule monitors the OBI handshake, which consists of a request and a response.
The request can contain attributes that affect the response.
This module aims to monitor an attribute of the request, and when receiving the corresponding response, output the response's request's attribute value.

What complicates the described task is that a request is not always directly followed by a response.
In other words, we need to keep track of which request belongs to which response.

The module uses a FIFO to keep track of the requests and the responses.
The FIFO can only hold 2 requests at once.
The figure shows how the FIFO behaves when requests are generated ((gnt && reg)==1) and responses are received (rvalid==1).
In the figure, the FIFO is the container, the pointer is illustrated as a ^, and rN is the request number N's attribute value.
The attribute value in FIFO[2] is read whenever rvalid==1.


t1:            |  t2:            |  t3:            |
gnt && req     |  gnt && req     |  !(gnt && req)  |
&& !rvalid     |  && !rvalid     |  && !rvalid     |
_____________  |  _____________  |  _____________  |
|   |   |   |  |  |   |   |   |  |  |   |   |   |  |
| X |   |   |  |  | X |   | r1|  |  | X | r2| r1|  |
|___|___|___|  |  |___|___|___|  |  |___|___|___|  |
          ^             ^             ^

t4:            |  t5:            |  t6:            |
!(gnt && req)  |  !(gnt && req)  |  !(gnt && req)  |
&& rvalid      |  && rvalid      |  && !rvalid     |
_____________  |  _____________  |  _____________  |
|   |   |   |  |  |   |   |   |  |  |   |   |   |  |
| X | r2| r1|  |  | X |   | r2|  |  | X |   |   |  |
|___|___|___|  |  |___|___|___|  |  |___|___|___|  |
  ^                     ^                     ^

t7:            |  t8:            |  t9:            |
gnt && req     |  gnt && req     |  !(gnt && req)  |
&& !rvalid     |  && rvalid      |  && !rvalid     |
_____________  |  _____________  |  _____________  |
|   |   |   |  |  |   |   |   |  |  |   |   |   |  |
| X |   |   |  |  | X |   | r3|  |  | X |   | r4|  |
|___|___|___|  |  |___|___|___|  |  |___|___|___|  |
          ^             ^                 ^

*/


module uvmt_cv32e40s_sl_req_attribute_fifo
  (
    input logic rst_ni,
    input logic clk_i,

    //OBI handshake signals
    input logic gnt,
    input logic req,
    input logic rvalid,

    //Attribute in the current request
    input logic req_attribute_i,

    //Indicates if the response's request contained the attribute or not
    output logic is_req_attribute_in_response_o
  );

  logic [2:0] fifo;
  logic [1:0] pointer;

  assign is_req_attribute_in_response_o = rvalid && fifo[2];

  always @(posedge clk_i, negedge rst_ni) begin
    if(!rst_ni) begin
      fifo <= 3'b000;
      pointer = 2;
    end else begin

      //This logic is demonstrated in time t1, t2 and t3 in the figure above
      if ((gnt && req) && !rvalid) begin
        fifo[pointer] <= req_attribute_i;
        pointer <= pointer - 1;

      //This logic is demonstrated in time t4, t5 and t6 in the figure above
      end else if (!(gnt && req) && rvalid) begin
        pointer <= pointer + 1;
        fifo <= {fifo[1:0], 1'b0};

      //This logic is demonstrated in time t8 and t9 in the figure above (and uses t7 to generate a situation where this part of the logic can be used)
      end else if ((gnt && req) && rvalid) begin
        fifo[pointer] <= req_attribute_i;
        fifo <= {fifo[1:0], 1'b0};

      end
    end
  end

endmodule : uvmt_cv32e40s_sl_req_attribute_fifo

