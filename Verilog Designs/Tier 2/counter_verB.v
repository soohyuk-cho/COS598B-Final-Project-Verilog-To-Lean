// ------------------------------------------------------------
// Counter Variant B - A Loadable Counter
// Author: SooHyuk Cho
// ------------------------------------------------------------
// A loadable counter with synchronous active-high reset.
// A loadable counter in Verilog is a sequential circuit 
// that counts up or down on a clock edge, with an added functionality 
// to preset its register to a specific, user-defined value when a "load" signal is enabled
//
// Priority on each rising edge of clk:
//   1. rst  -> count := 0
//   2. load -> count := load_value
//   3. en   -> count := count + 1
//   4. else hold
//
// This module is useful for testing whether a translator preserves
// control priority exactly.
// ------------------------------------------------------------

module counter_loadable #(
    parameter WIDTH = 8
) (
    input clk,
    input rst,
    input load,
    input en,
    input [WIDTH-1:0] load_value,
    output reg [WIDTH-1:0] count
);

always @(posedge clk) begin
    if (rst) begin
        count <= {WIDTH{1'b0}};
    end else if (load) begin
        count <= load_value;
    end else if (en) begin
        count <= count + 1'b1;
    end else begin
        count <= count;
    end
end

endmodule