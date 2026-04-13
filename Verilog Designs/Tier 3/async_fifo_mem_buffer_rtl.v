module async_fifo #(
    parameter DATA_WIDTH = 8,
    parameter FIFO_DEPTH = 16,
    parameter ADDR_WIDTH = $clog2(FIFO_DEPTH)
)(
    input wire                    wr_clk,     // Write clock
    input wire                    rd_clk,     // Read clock
    input wire                    wr_rst_n,   // Write reset (active low)
    input wire                    rd_rst_n,   // Read reset (active low)
    input wire                    wr_en,      // Write enable
    input wire                    rd_en,      // Read enable
    input wire  [DATA_WIDTH-1:0]  wr_data,    // Data to write
    output reg  [DATA_WIDTH-1:0]  rd_data,    // Data read
    output wire                   full,       // FIFO full flag
    output wire                   empty       // FIFO empty flag
);

    // FIFO memory
    reg [DATA_WIDTH-1:0] mem [FIFO_DEPTH-1:0];

    // Write and read pointers
    reg [ADDR_WIDTH:0] wr_ptr_bin, wr_ptr_gray, wr_ptr_gray_sync;
    reg [ADDR_WIDTH:0] rd_ptr_bin, rd_ptr_gray, rd_ptr_gray_sync;

    // Write pointer synchronization (to read clock domain)
    always @(posedge read_clk or negedge rd_rst_n) begin
        if (!rd_rst_n) begin
            wr_ptr_gray_sync <= 0;
        end else begin
            wr_ptr_gray_sync <= wr_ptr_gray;
        end
    end

    // Read pointer synchronization (to write clock domain)
    always @(posedge wr_clk or negedge wr_rst_n) begin
        if (!wr_rst_n) begin
            rd_ptr_gray_sync <= 0;
        end else begin
            rd_ptr_gray_sync <= rd_ptr_gray;
        end
    end

    // Convert pointers from Gray code to binary
    function [ADDR_WIDTH:0] gray_to_bin(input [ADDR_WIDTH:0] gray);
        integer i;
        begin
            gray_to_bin[ADDR_WIDTH] = gray[ADDR_WIDTH];
            for (i = ADDR_WIDTH-1; i >= 0; i = i-1) begin
                gray_to_bin[i] = gray_to_bin[i+1] ^ gray[i];
            end
        end
    endfunction

    wire [ADDR_WIDTH:0] wr_ptr_bin_sync = gray_to_bin(wr_ptr_gray_sync);
    wire [ADDR_WIDTH:0] rd_ptr_bin_sync = gray_to_bin(rd_ptr_gray_sync);

    // Write logic
    always @(posedge wr_clk or negedge wr_rst_n) begin
        if (!wr_rst_n) begin
            wr_ptr_bin <= 0;
            wr_ptr_gray <= 0;
        end else if (wr_en && !full) begin
            mem[wr_ptr_bin[ADDR_WIDTH-1:0]] <= wr_data;
            wr_ptr_bin <= wr_ptr_bin + 1;
            wr_ptr_gray <= (wr_ptr_bin + 1) ^ ((wr_ptr_bin + 1) >> 1);
        end
    end

    // Read logic
    always @(posedge rd_clk or negedge rd_rst_n) begin
        if (!rd_rst_n) begin
            rd_ptr_bin <= 0;
            rd_ptr_gray <= 0;
            rd_data <= 0;
        end else if (rd_en && !empty) begin
            rd_data <= mem[rd_ptr_bin[ADDR_WIDTH-1:0]];
            rd_ptr_bin <= rd_ptr_bin + 1;
            rd_ptr_gray <= (rd_ptr_bin + 1) ^ ((rd_ptr_bin + 1) >> 1);
        end
    end

    // Full and empty flag generation
    assign full = (wr_ptr_gray == {~rd_ptr_bin_sync[ADDR_WIDTH], rd_ptr_bin_sync[ADDR_WIDTH-1:0]});
    assign empty = (wr_ptr_bin_sync == rd_ptr_gray);

endmodule
