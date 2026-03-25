`timescale 1ns/1ps

// ------------------------------------------------------------
// Accumulator Variant ㅠ - Accumulator with add/sub control
// Author: SooHyuk Cho
// ------------------------------------------------------------
// A simple accumulator with synchronous active-high reset,
// enable, and add/sub control.
//
// Behavior on each rising edge of clk:
//   1. If rst=1, clear the accumulator to 0.
//   2. Else if en=1:
//        - if sub=0, add  data_in to the accumulator
//        - if sub=1, subtract data_in from the accumulator
//   3. Else, hold the current value.
//
// Arithmetic is performed modulo 2^WIDTH, since sum_out has a
// fixed bit width.
//
// This module is useful for testing whether a translator
// correctly preserves control-dependent arithmetic updates.
// ------------------------------------------------------------

module accumulator_addsub #(
    parameter WIDTH = 8
) (
    input clk,
    input rst,
    input en,
    input sub,
    input  [WIDTH-1:0] data_in,
    output reg [WIDTH-1:0] sum_out
);

always @(posedge clk) begin
    if (rst) begin
        // Highest priority: synchronous reset
        sum_out <= {WIDTH{1'b0}};
    end else if (en) begin
        // When enabled, choose add or subtract based on sub
        if (sub)
            sum_out <= sum_out - data_in;
        else
            sum_out <= sum_out + data_in;
    end else begin
        // Explicit hold behavior
        sum_out <= sum_out;
    end
end

endmodule