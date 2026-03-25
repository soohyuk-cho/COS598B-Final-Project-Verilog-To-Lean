`timescale 1ns/1ps

// ------------------------------------------------------------
// FSM Var A - fsm_toggle
// Author: SooHyuk Cho
// ------------------------------------------------------------
// A 2-state Moore FSM.
//
// States:
//   S0 : output state_out = 0
//   S1 : output state_out = 1
//
// Transition behavior on each rising edge of clk:
//   1. If rst=1, go to S0.
//   2. Else if toggle=1, switch to the other state.
//   3. Else, remain in the current state.
//
// This is a very small sequential fsm that is useful for
// testing whether translation preserves:
//   - explicit state encoding
//   - reset behavior
//   - next-state logic
//   - output logic derived from current state
// ------------------------------------------------------------

module fsm_toggle (
    input clk,
    input rst,
    input toggle,
    output reg state_out
);

localparam S0 = 1'b0;
localparam S1 = 1'b1;

reg state;

always @(posedge clk) begin
    if (rst) begin
        state <= S0;
    end else begin
        case (state)
            S0: begin
                if (toggle)
                    state <= S1;
                else
                    state <= S0;
            end

            S1: begin
                if (toggle)
                    state <= S0;
                else
                    state <= S1;
            end

            default: begin
                state <= S0;
            end
        endcase
    end
end

// Moore output logic: depends only on current state
always @(*) begin
    case (state)
        S0: state_out = 1'b0;
        S1: state_out = 1'b1;
        default: state_out = 1'b0;
    endcase
end

endmodule