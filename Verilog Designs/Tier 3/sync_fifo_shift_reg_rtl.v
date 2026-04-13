module synchronous_shift_register_fifo #(
    parameter WIDTH = 8,   // Data width
    parameter DEPTH = 4    // FIFO depth
)(
    input  wire                 clk,        // Clock signal
    input  wire                 rst,        // Reset signal (active high)
    input  wire                 write_en,   // Write enable
    input  wire                 read_en,    // Read enable
    input  wire [WIDTH-1:0]     data_in,    // Data input
    output reg  [WIDTH-1:0]     data_out,   // Data output
    output wire                 full,       // FIFO full flag
    output wire                 empty       // FIFO empty flag
);

    // Internal shift register storage
    reg [WIDTH-1:0] shift_reg [0:DEPTH-1];
    reg [$clog2(DEPTH+1)-1:0] count; // Tracks the number of elements

    integer i;

    // Assign full and empty flags based on the count
    assign full  = (count == DEPTH);
    assign empty = (count == 0);

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            // Reset all registers and count
            count    <= 0;
            data_out <= {WIDTH{1'b0}};
            for (i = 0; i < DEPTH; i = i + 1) begin
                shift_reg[i] <= {WIDTH{1'b0}};
            end
        end else begin
            // Read operation
            if (read_en && !empty) begin
                data_out <= shift_reg[count - 1];
            end

            // Shift data for write operation
            if (write_en && !full) begin
                for (i = count; i > 0; i = i - 1) begin
                    shift_reg[i] <= shift_reg[i - 1];
                end
                shift_reg[0] <= data_in;
            end

            // Update count based on read and write enables
            case ({write_en && !full, read_en && !empty})
                2'b10: count <= count + 1; // Write only
                2'b01: count <= count - 1; // Read only
                2'b11: count <= count;     // Simultaneous read and write
                default: count <= count;   // No operation
            endcase
        end
    end

endmodule
