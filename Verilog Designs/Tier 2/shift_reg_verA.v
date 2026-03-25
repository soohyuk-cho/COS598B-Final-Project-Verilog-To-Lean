`timescale 1ns/1ps

// ------------------------------------------------------------
// Shift Register Variant A - Left-Shifting Serial-In Register
// Author: SooHyuk Cho
// ------------------------------------------------------------
// A left-shifting register with synchronous active-high reset.
//
// Behavior on each rising edge of clk:
//   1. If rst=1, clear the register to 0.
//   2. Else if en=1, shift all bits left by one position.
//      The new least-significant bit (LSB) is filled with
//      the serial input bit 'shift_in'.
//   3. Else, hold the current value.
//
// Example for WIDTH=4:
//   current  = 4'b1010
//   shift_in = 1'b1
//   next     = 4'b0101
//
// because:
//   next[3:1] = current[2:0]
//   next[0]   = shift_in
// ------------------------------------------------------------

module shiftreg_left #(
    parameter WIDTH = 8
) (
    input clk,
    input rst,
    input en,
    input shift_in,
    output reg [WIDTH-1:0] data_out
);

always @(posedge clk) begin
    if (rst) begin
        // Highest priority: reset clears the whole register
        data_out <= {WIDTH{1'b0}};
    end else if (en) begin
        // Shift left by one bit.
        // Drop the old MSB, move remaining bits upward,
        // and insert shift_in into the LSB position.
        data_out <= {data_out[WIDTH-2:0], shift_in};
    end else begin
        // Explicit hold behavior
        data_out <= data_out;
    end
end

endmodule