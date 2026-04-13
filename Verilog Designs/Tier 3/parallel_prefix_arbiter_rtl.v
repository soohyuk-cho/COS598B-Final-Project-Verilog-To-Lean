// Author: SooHyuk Cho
module parallel_prefix_arbiter_v1 #(
    parameter int NUM_REQUESTS = 8
)(
    input  logic                   clk,
    input  logic                   reset,
    input  logic [NUM_REQUESTS-1:0] req,  
    output logic [NUM_REQUESTS-1:0] grant
);

    // Generate unique priority for each requester (0 highest, NUM_REQUESTS-1 lowest)
    typedef struct {
        logic valid;
        int  priority;
    } request_t;
    
    request_t requests [NUM_REQUESTS-1:0];
    
    // Assign priorities based on index (lower index = higher priority)
    integer i;
    initial begin
        for (i = 0; i < NUM_REQUESTS; i++) begin
            requests[i].valid = 0;
            requests[i].priority = i;
        end
        grant = '0;
    end
    
    // Process requests on each clock cycle
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            for (i = 0; i < NUM_REQUESTS; i++) begin
                requests[i].valid <= 0;
                requests[i].priority <= i;
            end
            grant <= '0;
        end else begin
            // Update request validity
            for (i = 0; i < NUM_REQUESTS; i++) begin
                requests[i].valid <= req[i];
            end
            
            // Parallel Prefix Network to find the highest priority request
            // Step 1: Generate propagate and generate signals
            logic [NUM_REQUESTS-1:0] propagate, gen;
            for (i = 0; i < NUM_REQUESTS; i++) begin
                propagate[i] = requests[i].valid;
                gen[i] = requests[i].valid;
            end
            
            // Step 2: Perform parallel prefix computation
            // Using a simplified Kogge-Stone for demonstration
            // Note: For large NUM_REQUESTS, more optimized implementations are needed
            logic [NUM_REQUESTS-1:0] p_stage1, g_stage1;
            logic [NUM_REQUESTS-1:0] p_stage2, g_stage2;
            logic [NUM_REQUESTS-1:0] p_stage3, g_stage3;
            
            // Stage 1
            for (i = 0; i < NUM_REQUESTS; i++) begin
                if (i >= 1) begin
                    p_stage1[i] = p_stage1[i] & p_stage1[i-1];
                    g_stage1[i] = g_stage1[i] | (p_stage1[i] & g_stage1[i-1]);
                end else begin
                    p_stage1[i] = propagate[i];
                    g_stage1[i] = gen[i];
                end
            end
            
            // Stage 2
            for (i = 0; i < NUM_REQUESTS; i++) begin
                if (i >= 2) begin
                    p_stage2[i] = p_stage2[i] & p_stage2[i-2];
                    g_stage2[i] = g_stage2[i] | (p_stage2[i] & g_stage2[i-2]);
                end else begin
                    p_stage2[i] = p_stage1[i];
                    g_stage2[i] = g_stage1[i];
                end
            end
            
            // Stage 3
            for (i = 0; i < NUM_REQUESTS; i++) begin
                if (i >= 4) begin
                    p_stage3[i] = p_stage3[i] & p_stage3[i-4];
                    g_stage3[i] = g_stage3[i] | (p_stage3[i] & g_stage3[i-4]);
                end else begin
                    p_stage3[i] = p_stage2[i];
                    g_stage3[i] = g_stage2[i];
                end
            end
            
            // Determine the highest priority request
            // The highest priority request is the first one with generate signal
            grant = '0;
            for (i = 0; i < NUM_REQUESTS; i++) begin
                if (g_stage3[i]) begin
                    grant[i] = 1;
                    disable for_loop;
                end
            end
        end
    end

endmodule