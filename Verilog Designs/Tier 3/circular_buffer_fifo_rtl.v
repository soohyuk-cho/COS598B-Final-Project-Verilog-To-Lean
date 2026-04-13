module circular_buffer #(
    parameter DATA_WIDTH = 8,           
    parameter BUFFER_SIZE = 16,         
    parameter ADDR_WIDTH = 4            
)(
    input  wire                   clk,      
    input  wire                   reset,    

    input  wire                   wr_en,    
    input  wire [DATA_WIDTH-1:0]  wr_data,  

    input  wire                   rd_en,    
    output reg  [DATA_WIDTH-1:0]  rd_data, 

    output wire                   full,    
    output wire                   empty     
);

    // Memory array to store data
    reg [DATA_WIDTH-1:0] mem [0:BUFFER_SIZE-1];

    // Read and write pointers
    reg [ADDR_WIDTH-1:0] rd_ptr;  // Read pointer
    reg [ADDR_WIDTH-1:0] wr_ptr;  // Write pointer

    // Full and empty indicators
    reg full_flag;
    reg empty_flag;

    // Calculate next pointers
    wire [ADDR_WIDTH-1:0] rd_ptr_next = rd_ptr + 1;
    wire [ADDR_WIDTH-1:0] wr_ptr_next = wr_ptr + 1;

    // Write Operation
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            wr_ptr    <= 0;
            full_flag <= 1'b0;
        end else if (wr_en && !full_flag) begin
            mem[wr_ptr] <= wr_data;
            wr_ptr      <= wr_ptr_next;
            // Update full flag
            if (wr_ptr_next == rd_ptr)
                full_flag <= 1'b1;
            empty_flag <= 1'b0;  // Buffer is not empty anymore
        end
    end

    // Read Operation
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            rd_ptr     <= 0;
            empty_flag <= 1'b1;
        end else if (rd_en && !empty_flag) begin
            rd_data <= mem[rd_ptr];
            rd_ptr  <= rd_ptr_next;
            // Update empty flag
            if (wr_ptr == rd_ptr_next)
                empty_flag <= 1'b1;
            full_flag <= 1'b0; 
        end
    end

    // Output assignments
    assign full  = full_flag;
    assign empty = empty_flag;

endmodule
