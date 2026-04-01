module ALU_4 (
    input  wire [3:0] lhs,
    input  wire [3:0] rhs,
    input  wire [1:0] op,
    output reg  [3:0] out
);
    always @(*) begin
        case (op)
            2'b00: out = lhs + rhs;
            2'b01: out = lhs - rhs;
            2'b10: out = lhs & rhs;
            2'b11: out = lhs | rhs;
        endcase
    end
endmodule
