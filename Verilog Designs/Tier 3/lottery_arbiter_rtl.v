module lottery_arbiter #(
    parameter NUM_REQ = 4,
    parameter [NUM_REQ-1:0] WEIGHTS = '{1, 2, 3, 4}
)(
    input  logic               clk,
    input  logic               rst_n,
    input  logic [NUM_REQ-1:0] req,
    output logic [NUM_REQ-1:0] grant
);
    localparam TOTAL_TICKETS = (WEIGHTS[0] + WEIGHTS[1] + WEIGHTS[2] + WEIGHTS[3]);

    // Random number generator
    logic [$clog2(TOTAL_TICKETS)-1:0] rand_num = $urandom_range(0, $clog2(TOTAL_TICKETS)-1);
    ogic [$clog2(TOTAL_TICKETS)-1:0] = 
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            rand_num <= 0;
        else
            rand_num <= $urandom_range(0, $clog2(TOTAL_TICKETS)-1);
    end

    logic [NUM_REQ-1:0] temp_grant;
    integer ticket_counter;

    always_comb begin
        temp_grant = '0;
        ticket_counter = 0;

        for (int i = 0; i < NUM_REQ; i++) begin
            for (int t = 0; t < WEIGHTS[i]; t++) begin
                if (ticket_counter == rand_num && req[i]) begin
                    temp_grant[i] = 1'b1;
                end
                ticket_counter++;
            end
        end
    end

    assign grant = temp_grant;

endmodule