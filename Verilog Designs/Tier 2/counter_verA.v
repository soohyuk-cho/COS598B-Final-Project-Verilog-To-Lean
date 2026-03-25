// --------------------------------------------------------------------------------
// Counter Variant A - Simple Wraparound Counter
// Author: SooHyuk Cho
// --------------------------------------------------------------------------------
// A simple wraparound up-counter with synchronous active-high reset and enable.
//
// Behavior on each rising edge of clk:
//   1. If rst=1, count resets to 0.
//   2. Else if en=1, count increments by 1.
//   3. Else, count holds its previous value.
//
// Since count has finite width, increment naturally wraps around on overflow.
// --------------------------------------------------------------------------------
module counter_wrap #(
    parameter WIDTH = 8
) (
    input clk,
    input rst,
    input en,
    output reg [WIDTH-1:0] count
);

always @(posedge clk) begin
   if (rst) begin
        count <= {WIDTH{1'b0}};
    end else if (en) begin
        count <= count + 1'b1;
    end else begin
        count <= count;
    end
end

endmodule