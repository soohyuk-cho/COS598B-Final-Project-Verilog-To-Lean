module async_shift_register_fifo #(
    parameter WIDTH = 8,    // Data width
    parameter DEPTH = 16    // FIFO depth (must be a power of 2)
)(
    input  wire              wr_clk,    // Write clock
    input  wire              rd_clk,    // Read clock
    input  wire              rst,       // Asynchronous reset (active high)
    input  wire              write_en,  // Write enable
    input  wire              read_en,   // Read enable
    input  wire [WIDTH-1:0]  data_in,   // Data input
    output reg  [WIDTH-1:0]  data_out,  // Data output
    output wire              full,      // FIFO full flag
    output wire              empty      // FIFO empty flag
);

    // Calculate the address width
    localparam ADDR_WIDTH = $clog2(DEPTH);

    // Shift register memory
    reg [WIDTH-1:0] fifo_mem [0:DEPTH-1];

    // Pointers in Gray code
    reg [ADDR_WIDTH:0] wr_ptr_bin, wr_ptr_gray;
    reg [ADDR_WIDTH:0] rd_ptr_bin, rd_ptr_gray;

    // Synchronized pointers
    reg [ADDR_WIDTH:0] wr_ptr_gray_sync1, wr_ptr_gray_sync2;
    reg [ADDR_WIDTH:0] rd_ptr_gray_sync1, rd_ptr_gray_sync2;

    // Internal signals
    wire [ADDR_WIDTH:0] wr_ptr_gray_next, rd_ptr_gray_next;
    wire [ADDR_WIDTH:0] wr_ptr_bin_next, rd_ptr_bin_next;

    // Reset and synchronization logic
    integer i;
    always @(posedge wr_clk or posedge rst) begin
        if (rst) begin
            wr_ptr_bin  <= 0;
            wr_ptr_gray <= 0;
            for (i = 0; i < DEPTH; i = i + 1) begin
                fifo_mem[i] <= {WIDTH{1'b0}};
            end
        end else begin
            // Write operation
            if (write_en && !full) begin
                fifo_mem[wr_ptr_bin[ADDR_WIDTH-1:0]] <= data_in;
                wr_ptr_bin  <= wr_ptr_bin_next;
                wr_ptr_gray <= wr_ptr_gray_next;
            end
        end
    end

    always @(posedge rd_clk or posedge rst) begin
        if (rst) begin
            rd_ptr_bin  <= 0;
            rd_ptr_gray <= 0;
            data_out    <= {WIDTH{1'b0}};
        end else begin
            // Read operation
            if (read_en && !empty) begin
                data_out    <= fifo_mem[rd_ptr_bin[ADDR_WIDTH-1:0]];
                rd_ptr_bin  <= rd_ptr_bin_next;
                rd_ptr_gray <= rd_ptr_gray_next;
            end
        end
    end

    // Next pointer calculations
    assign wr_ptr_bin_next  = wr_ptr_bin + (write_en && !full);
    assign wr_ptr_gray_next = (wr_ptr_bin_next >> 1) ^ wr_ptr_bin_next;

    assign rd_ptr_bin_next  = rd_ptr_bin + (read_en && !empty);
    assign rd_ptr_gray_next = (rd_ptr_bin_next >> 1) ^ rd_ptr_bin_next;

    // Synchronize pointers across clock domains
    always @(posedge wr_clk or posedge rst) begin
        if (rst) begin
            rd_ptr_gray_sync1 <= 0;
            rd_ptr_gray_sync2 <= 0;
        end else begin
            rd_ptr_gray_sync1 <= rd_ptr_gray;
            rd_ptr_gray_sync2 <= rd_ptr_gray_sync1;
        end
    end

    always @(posedge rd_clk or posedge rst) begin
        if (rst) begin
            wr_ptr_gray_sync1 <= 0;
            wr_ptr_gray_sync2 <= 0;
        end else begin
            wr_ptr_gray_sync1 <= wr_ptr_gray;
            wr_ptr_gray_sync2 <= wr_ptr_gray_sync1;
        end
    end

    // Generate full flag
    wire [ADDR_WIDTH:0] wr_ptr_gray_sync_rd_clk;
    assign wr_ptr_gray_sync_rd_clk = wr_ptr_gray_sync2;

    assign full = (wr_ptr_gray_next == {~rd_ptr_gray_sync2[ADDR_WIDTH:ADDR_WIDTH-1], rd_ptr_gray_sync2[ADDR_WIDTH-2:0]});

    // Generate empty flag
    wire [ADDR_WIDTH:0] rd_ptr_gray_sync_wr_clk;
    assign rd_ptr_gray_sync_wr_clk = rd_ptr_gray_sync2;

    assign empty = (rd_ptr_gray_next == wr_ptr_gray_sync_rd_clk);

endmodule
