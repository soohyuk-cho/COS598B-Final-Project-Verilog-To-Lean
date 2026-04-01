module Mux_2_1 (
    input  wire in0,
    input  wire in1,
    input  wire sel,
    output reg  out
);
    always @(*) begin
        case (sel)
            1'b0: out = in0;
            1'b1: out = in1;
            default: out = 1'b0;
        endcase
    end
endmodule
