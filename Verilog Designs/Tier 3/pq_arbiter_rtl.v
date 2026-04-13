// Author: SooHyuk Cho

module pq_arbiter_v1 #(
    parameter int NUM_REQUESTS = 4
)(
    input  logic                   clk,
    input  logic                   reset,
    input  logic [NUM_REQUESTS-1:0] req,
    output logic [NUM_REQUESTS-1:0] grant
);

    // Define priority levels (0 is highest) => MLPQ
    // Example: Requester 0 has highest priority, Requester 3 lowest
    localparam PRIORITY_WIDTH = $clog2(NUM_REQUESTS);
    
    // Queues for each priority level
    // Simple FIFO queues implemented as circular buffers
    typedef struct {
        logic [NUM_REQUESTS-1:0] queue;
        int head;
        int tail;
    } fifo_t;
    
    fifo_t request_queue [NUM_REQUESTS-1:0];
    
    integer i;
    
    // Initialize queues
    initial begin
        for (i = 0; i < NUM_REQUESTS; i++) begin
            request_queue[i].queue = '0;
            request_queue[i].head = 0;
            request_queue[i].tail = 0;
        end
        grant = '0;
    end
    
    // Enqueue incoming requests
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            for (i = 0; i < NUM_REQUESTS; i++) begin
                request_queue[i].queue <= '0;
                request_queue[i].head <= 0;
                request_queue[i].tail <= 0;
            end
            grant <= '0;
        end else begin
            // Enqueue new requests
            for (i = 0; i < NUM_REQUESTS; i++) begin
                if (req[i] && !request_queue[i].queue[i]) begin
                    request_queue[i].queue[i] <= 1;
                    // Simple enqueue by setting the bit; for real FIFO, more logic is needed
                end
            end
            
            // Grant access based on priority and queue
            grant <= '0;
            for (i = 0; i < NUM_REQUESTS; i++) begin
                if (request_queue[i].queue[i]) begin
                    grant[i] <= 1;
                    request_queue[i].queue[i] <= 0; // Dequeue after granting
                    break; // Grant only one request per cycle
                end
            end
        end
    end

endmodule