module Decoder_2_4 (
    input  wire [1:0] in,
    output wire [3:0] out
);
    assign out = 4'b0001 << in;
endmodule
