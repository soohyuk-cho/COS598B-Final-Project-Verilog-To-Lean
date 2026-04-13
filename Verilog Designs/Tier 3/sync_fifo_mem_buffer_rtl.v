module sync_fifo #(parameter WIDTH = 32, parameter LOGDEPTH = 3) (
    input clk,
    input reset,

    input enq_val,
    input [WIDTH-1:0] enq_data,
    output enq_rdy,
    output deq_val,
    output [WIDTH-1:0] deq_data,
    input deq_rdy
);

localparam DEPTH = (1 << LOGDEPTH);

// the buffer itself. Take note of the 2D syntax.
reg [WIDTH-1:0] buffer [DEPTH-1:0];
// read pointer, write pointer
reg [LOGDEPTH-1:0] rptr, wptr;
// is the buffer full? This is needed for when rptr == wptr
reg full;

// Define any additional regs or wires you need (if any) here
reg [WIDTH-1:0] deq_data_reg;
// use "fire" to indicate when a valid transaction has been made
wire enq_fire;
wire deq_fire;

assign enq_fire = enq_val & enq_rdy;
assign deq_fire = deq_val & deq_rdy;

// Your code here (don't forget the reset!)

// enq_rdy is still ready when the buffer is not full
assign enq_rdy = !full;

//deq is not valid if the pointers are equal and the buffer is not full
assign deq_val = !(rptr == wptr && !full);

//assign deq_data = deq_data_reg;
assign deq_data = buffer[rptr];

always @(posedge clk, posedge reset) begin
    if (reset) begin
        rptr <=0;
        wptr <=0;
        full <=0;
        deq_data_reg <=0;
    end else if (enq_fire) begin
        buffer[wptr] <= enq_data;
        wptr <= wptr + 1;
        if (wptr == rptr) begin
            full <= 1;
        end else begin
            full <=0;
        end
    end else if (deq_fire) begin
        rptr <= rptr + 1;
        full <= 0;
    end
end

endmodule