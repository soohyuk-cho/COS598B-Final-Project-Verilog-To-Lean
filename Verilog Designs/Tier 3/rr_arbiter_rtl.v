module rr_arbiter_v1 #(
    parameter NUM_REQ = 4
)(
    input  logic                 clk,      
    input  logic                 rst_n,    
    input  logic [NUM_REQ-1:0]   req,      
    output logic [NUM_REQ-1:0]   grant
);

    localparam PTR_WIDTH = $clog2(NUM_REQ);

    logic [PTR_WIDTH-1:0] rotate_ptr;

    logic [NUM_REQ-1:0] grant_next;
    logic [PTR_WIDTH-1:0] next_ptr;

    always_comb begin
        // Initialize grants to zero
        grant_next = '0;
        next_ptr   = rotate_ptr;

        // Iterate through all requesters starting from rotate_ptr
        for (int i = 0; i < NUM_REQ; i++) begin
            // Calculate the index with wrap-around
            int idx = (rotate_ptr + i) % NUM_REQ;
            if (req[idx] && grant_next == '0) begin
                grant_next[idx] = 1'b1; // Grant to the first active requester
                next_ptr = (idx + 1) % NUM_REQ; // Update pointer for next cycle
            end
        end
    end

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            grant <= '0;
            rotate_ptr <= '0;
        end
        else begin
            grant <= grant_next;
            if (|grant_next)
                rotate_ptr <= next_ptr;
        end
    end

endmodule