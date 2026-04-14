module Encoder_4_2_verB (
    input  wire [3:0] in,
    output wire [1:0] out
);
    assign out[1] = in[2] | in[3];
    assign out[0] = in[1] | in[3];
endmodule
