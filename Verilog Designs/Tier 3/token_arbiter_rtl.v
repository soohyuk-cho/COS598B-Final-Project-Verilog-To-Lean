// Author: SooHyuk Cho

module token_arbiter_v1 (
    input wire clk,
    input wire reset,
    input wire [3:0] req,      // 4 requesters
    output reg [3:0] grant
);
    reg [3:0] token;            // One-hot encoded token

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            token <= 4'b0001;   // Initialize token to Requester 0
            grant <= 4'b0000;
        end else begin
            grant <= 4'b0000;
            
            // Grant access to the requester holding the token if it requests
            if (token[0] && req[0]) begin
                grant <= 4'b0001;
                token <= 4'b0010; // Pass token to Requester 1
            end else if (token[1] && req[1]) begin
                grant <= 4'b0010;
                token <= 4'b0100; // Pass token to Requester 2
            end else if (token[2] && req[2]) begin
                grant <= 4'b0100;
                token <= 4'b1000; // Pass token to Requester 3
            end else if (token[3] && req[3]) begin
                grant <= 4'b1000;
                token <= 4'b0001; // Pass token back to Requester 0
            end else begin
                // If current token holder is not requesting, pass the token to the next requester
                token <= {token[2:0], token[3]};
            end
        end
    end
endmodule