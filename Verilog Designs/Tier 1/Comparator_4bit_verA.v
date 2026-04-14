module Comparator_4_verA (
    input  wire [3:0] lhs,
    input  wire [3:0] rhs,
    output wire       lt,
    output wire       eq,
    output wire       gt
);
    assign lt = (lhs < rhs);
    assign eq = (lhs == rhs);
    assign gt = (lhs > rhs);
endmodule
