`timescale 1ns/1ps

// ------------------------------------------------------------
// FSM Var B - fsm_handshake_3state
// Author: SooHyuk Cho
// ------------------------------------------------------------
// A small 3-state Moore FSM modeling a simple request/acknowledge
// controller.
//
// States:
//   IDLE: waiting for a request
//   WAIT_ACK: request observed, waiting for acknowledge
//   DONE_ST: acknowledge observed; emit done for one cycle
//
// Transition behavior on each rising edge of clk:
//   1. If rst=1, go to IDLE.
//   2. In IDLE:
//        - if req=1, go to WAIT_ACK
//        - else remain in IDLE
//   3. In WAIT_ACK:
//        - if ack=1, go to DONE_ST
//        - else remain in WAIT_ACK
//   4. In DONE_ST:
//        - go back to IDLE on the next cycle
//
// Outputs are Moore-style:
//   IDLE -> busy=0, done=0
//   WAIT_ACK -> busy=1, done=0
//   DONE_ST -> busy=0, done=1
//
// This module is useful for testing whether translation preserves:
//   - multi-state encoding
//   - explicit transition coverage
//   - Moore output logic
//   - one-cycle terminal state behavior
// ------------------------------------------------------------

module fsm_handshake_3state (
    input clk,
    input rst,
    input req,
    input ack,
    output reg busy,
    output reg done
);

localparam IDLE = 2'd0;
localparam WAIT_ACK = 2'd1;
localparam DONE_ST  = 2'd2;

reg [1:0] state;

always @(posedge clk) begin
    if (rst) begin
        state <= IDLE;
    end else begin
        case (state)
            IDLE: begin
                if (req)
                    state <= WAIT_ACK;
                else
                    state <= IDLE;
            end

            WAIT_ACK: begin
                if (ack)
                    state <= DONE_ST;
                else
                    state <= WAIT_ACK;
            end

            DONE_ST: begin
                state <= IDLE;
            end

            default: begin
                state <= IDLE;
            end
        endcase
    end
end

// Moore output logic: depends only on current state
always @(*) begin
    case (state)
        IDLE: begin
            busy = 1'b0;
            done = 1'b0;
        end

        WAIT_ACK: begin
            busy = 1'b1;
            done = 1'b0;
        end

        DONE_ST: begin
            busy = 1'b0;
            done = 1'b1;
        end

        default: begin
            busy = 1'b0;
            done = 1'b0;
        end
    endcase
end

endmodule