
module uvmt_cv32e40s_sl_obi_phases_monitor
  import uvm_pkg::*;
  (
    input logic clk_i,
    input logic rst_ni,

    input logic obi_req,
    input logic obi_gnt,
    input logic obi_rvalid,


    // continued address and respons phase indicators, indicates address and respons phases
    // of more than one cycle
    output logic addr_ph_cont,
    output logic resp_ph_cont,

    // address phase counter, used to verify no response phase preceedes an address phase
    output integer v_addr_ph_cnt
  );

  logic addr_ph_valid;
  logic rsp_ph_valid;
  logic obi_rready;

  assign obi_rready = 1'b1; //This is an assumption

  assign addr_ph_valid = obi_req == 1'b1 && obi_gnt == 1'b1;
  assign rsp_ph_valid = obi_rready == 1'b1 && obi_rvalid == 1'b1;


  always @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      addr_ph_cont <= 1'b0;
    end
    else begin
      if (obi_req == 1'b1 && obi_gnt == 1'b0) begin
        addr_ph_cont <= 1'b1;
      end
      else begin
        addr_ph_cont <= 1'b0;
      end
    end
  end

  always @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      resp_ph_cont <= 1'b0;
    end
    else begin
      if (obi_rvalid == 1'b1 && obi_rready == 1'b0) begin
        resp_ph_cont <= 1'b1;
      end
      else begin
        resp_ph_cont <= 1'b0;
      end
    end
  end

  always @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      v_addr_ph_cnt <= '0;
    end
    else begin
      if (addr_ph_valid && !rsp_ph_valid) begin
        v_addr_ph_cnt <= v_addr_ph_cnt + 1'b1;
      end
      else if (!addr_ph_valid && rsp_ph_valid && v_addr_ph_cnt > 0) begin
        v_addr_ph_cnt <= v_addr_ph_cnt - 1'b1;
      end
    end
  end
endmodule : uvmt_cv32e40s_sl_obi_phases_monitor
