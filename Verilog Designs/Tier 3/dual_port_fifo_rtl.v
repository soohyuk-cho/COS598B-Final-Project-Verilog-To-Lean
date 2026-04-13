module dual_port_fifo_v2 #(
    parameter DATA_WIDTH = 8,   // Data width
    parameter DEPTH = 16        // FIFO depth (must be a power of 2)
) (
    input wire clk,             // Clock signal
    input wire rst,             // Reset signal (active high)
    
    // Write Port
    input wire wr_en,           // Write enable
    input wire [DATA_WIDTH-1:0] wr_data, // Data to write
    output reg full,            // Full flag
    
    // Read Port
    input wire rd_en,           // Read enable
    output reg [DATA_WIDTH-1:0] rd_data, // Data read
    output reg empty            // Empty flag
);

    // Local Parameters
    localparam ADDR_WIDTH = $clog2(DEPTH); // Address width based on depth

    // Memory Array
    reg [DATA_WIDTH-1:0] fifo_mem [0:DEPTH-1];

    // Read and Write Pointers
    reg [ADDR_WIDTH:0] wr_ptr;  // Write pointer (1 extra bit for full/empty detection)
    reg [ADDR_WIDTH:0] rd_ptr;  // Read pointer (1 extra bit for full/empty detection)

    // Combinational logic to check status
    wire fifo_empty = (wr_ptr == rd_ptr);
    wire fifo_full = ((wr_ptr[ADDR_WIDTH] != rd_ptr[ADDR_WIDTH]) &&
                      (wr_ptr[ADDR_WIDTH-1:0] == rd_ptr[ADDR_WIDTH-1:0]));

    // Write Operation
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            wr_ptr <= 0;
        end else if (wr_en && !full) begin
            fifo_mem[wr_ptr[ADDR_WIDTH-1:0]] <= wr_data;
            wr_ptr <= wr_ptr + 1;
        end
    end

    // Read Operation
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            rd_ptr <= 0;
            rd_data <= 0;
        end else if (rd_en && !empty) begin
            rd_data <= fifo_mem[rd_ptr[ADDR_WIDTH-1:0]];
            rd_ptr <= rd_ptr + 1;
        end
    end

    // Status Flag Updates
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            full <= 0;
            empty <= 1;
        end else begin
            full <= fifo_full;
            empty <= fifo_empty;
        end
    end

endmodule
