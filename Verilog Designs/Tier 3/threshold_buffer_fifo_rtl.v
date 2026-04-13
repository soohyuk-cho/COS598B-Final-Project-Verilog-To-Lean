module threshold_fifo #(
    parameter DATA_WIDTH = 8,   // Width of the data bus
    parameter FIFO_DEPTH = 16   // Depth of the FIFO buffer
)(
    input  wire                    clk,                 
    input  wire                    reset,
    input  wire                    write_enable,        
    input  wire                    read_enable,         
    input  wire [DATA_WIDTH-1:0]   write_data,
    output wire [DATA_WIDTH-1:0]   read_data,
    output wire                    fifo_full,           
    output wire                    fifo_empty,          
    output wire                    high_threshold_reached, 
    output wire                    low_threshold_reached 
);

    localparam ADDR_WIDTH = $clog2(FIFO_DEPTH);

    // FIFO memory
    reg [DATA_WIDTH-1:0] fifo_mem [FIFO_DEPTH-1:0];

    // Pointers and count
    reg [ADDR_WIDTH-1:0] write_ptr = 0;
    reg [ADDR_WIDTH-1:0] read_ptr = 0;
    reg [ADDR_WIDTH:0]   fifo_count = 0;

    // Threshold values
    localparam HIGH_THRESHOLD = (FIFO_DEPTH * 80) / 100;  // 80% of capacity
    localparam LOW_THRESHOLD  = (FIFO_DEPTH * 20) / 100;  // 20% of capacity

    // Flags
    assign fifo_full = (fifo_count == FIFO_DEPTH);
    assign fifo_empty = (fifo_count == 0);
    assign high_threshold_reached = (fifo_count >= HIGH_THRESHOLD);
    assign low_threshold_reached = (fifo_count <= LOW_THRESHOLD);

    // Read/Write logic
    always @(posedge clk) begin
        if (reset) begin
            write_ptr  <= 0;
            read_ptr   <= 0;
            fifo_count <= 0;
        end else begin
            // Write operation
            if (write_enable && !fifo_full) begin
                fifo_mem[write_ptr] <= write_data;
                write_ptr           <= write_ptr + 1;
                fifo_count          <= fifo_count + 1;
            end

            // Read operation
            if (read_enable && !fifo_empty) begin
                read_data <= fifo_mem[read_ptr];
                read_ptr  <= read_ptr + 1;
                fifo_count <= fifo_count - 1;
            end
        end
    end

endmodule
