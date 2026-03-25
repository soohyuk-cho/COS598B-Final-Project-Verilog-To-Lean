`timescale 1ns/1ps

// ------------------------------------------------------------
// Accumulator Variant A - Accumulator with Enable and Reset
// Author: SooHyuk Cho
// ------------------------------------------------------------
// A simple accumulator with synchronous active-high reset.
//
// Behavior on each rising edge of clk:
//   1. If rst=1, clear the accumulator to 0.
//   2. Else if en=1, add 'data_in' to the current accumulator.
//   3. Else, hold the current value.
//
// This is useful for testing whether a translator correctly
// preserves arithmetic state updates and hold behavior.
// ------------------------------------------------------------

module accumulator_en #(
    parameter WIDTH = 8
) (
    input clk,
    input rst,
    input en,
    input [WIDTH-1:0] data_in,
    output reg  [WIDTH-1:0] sum_out
);

always @(posedge clk) begin
    if (rst) begin
        // Highest priority: reset
        sum_out <= {WIDTH{1'b0}};
    end else if (en) begin
        // Accumulate input into running sum
        sum_out <= sum_out + data_in;
    end else begin
        // Explicit hold
        sum_out <= sum_out;
    end
end

endmodule