module ALU_4 (
    input  wire [3:0] lhs,
    input  wire [3:0] rhs,
    input  wire [1:0] op,
    output wire [3:0] out
);
    wire [3:0] add_result;
    wire [3:0] sub_result;
    wire [3:0] and_result;
    wire [3:0] or_result;

    assign add_result = lhs + rhs;
    assign sub_result = lhs - rhs;
    assign and_result = lhs & rhs;
    assign or_result = lhs | rhs;

    assign out = (op == 2'b00) ? add_result :
                 (op == 2'b01) ? sub_result :
                 (op == 2'b10) ? and_result :
                                 or_result;
endmodule
