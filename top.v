/* Module is a slave connected to an AXI steam interface */

module top #(
	parameter AXI_DATA_W = 64,
	parameter AXI_KEEP_W = 8 // $clog2(AXI_DATA_W)
)(
	input clk,
	input nreset,
	
	// AXI stream interface from udp ethernet
	input [AXI_DATA_W-1:0] upd_axis_tdata_i,
	input [AXI_KEEP_W-1:0] upd_axis_tkeep_i,
	input                  upd_axis_tvalid_i,
	input                  upd_axis_tlast_i,
	input                  upd_axis_tuser_i,
	
	output                 upd_axis_tready_o,
);
// axi payload buffering ( for timing )
reg [AXI_DATA_W-1:0]  upd_axis_tdata_q;
reg [AXI_KEEP_W-1:0]  upd_axis_tkeep_q;
reg                   upd_axis_tvalid_q;
reg                   upd_axis_tlast_q;
reg                   upd_axis_tuser_q;
wire [AXI_DATA_W-1:0] upd_axis_tdata_next;
wire [AXI_KEEP_W-1:0] upd_axis_tkeep_next;
wire                  upd_axis_tvalid_next;
wire                  upd_axis_tlast_next;
wire                  upd_axis_tuser_next;

always @(posedge clk) 
begin
	if ( ~nreset ) begin
		upd_axis_tvalid_q  <= 1'b0;
	end else begin
		upd_axis_tdata_q   <= upd_axis_tdata_next; 	
		upd_axis_tkeep_q   <= upd_axis_tkeep_next;
		upd_axis_tvalid_q  <= upd_axis_tvalid_next;
		upd_axis_tlast_q   <= upd_axis_tlast_next;
		upd_axis_tuser_q   <= upd_axis_tuser_next;
	end
end

// 

// fsm
reg  fsm_invalid_q;
wire fsm_invalid_next;
// header 
// pX  : header is received over multiple cycles 
// msg : during last cycle part of the packed is the begining of the message
reg  fsm_header_h0_q;
reg  fsm_header_h1_q;
reg  fsm_header_h2_msg_q;
wire fsm_header_h0_next;
wire fsm_header_h1_next;
wire fsm_header_h2_msg_next;
// message
// message can be sent over multiple message modules m0 and m1
// mX      : denotes the module to which the start of the axi stream payload
//           will be sent
// overlap : part of the next axi payload is of a different modlupd64 message
//           it will be routed to the free moldupd64 module
reg  fsm_msg_m0_q;
reg  fsm_msg_m0_overlap_q;
reg  fsm_msg_m1_q;
reg  fsm_msg_m1_overlap_q;
wire fsm_msg_m0_next;
wire fsm_msg_m0_overlap_next;
wire fsm_msg_m1_next;
wire fsm_msg_m1_overlap_next;


assign fsm_header_h0_next     = fsm_invalid_q & upd_axis_tvalid_i;
assign fsm_header_h1_next     = fsm_header_h0_q;
assign fsm_header_h2_msg_next = fsm_header_h1_q; 

assign fsm_msg_m0_next = fsm_header_h2_msg_q; // default state
 
assign fsm_ms
always @(posedge clk)
begin
	if ( ~nreset ) begin
		fsm_invalid_q        <= 1'b1;
		fsm_header_h0_q      <= 1'b0;
		fsm_header_h1_q      <= 1'b0;
		fsm_header_h2_msg_q  <= 1'b0;
		fsm_msg_m0_q         <= 1'b0;
		fsm_msg_m0_overlap_q <= 1'b0;
		fsm_msg_m1_q         <= 1'b0;
		fsm_msg_m1_overlap_q <= 1'b0;	
		end else begin
		fsm_invalid_q        <= fsm_invalid_next; 
		fsm_header_h0_q      <= fsm_header_h0_next;     
		fsm_header_h1_q      <= fsm_header_h1_next;    
		fsm_header_h2_msg_q  <= fsm_header_h2_msg_next;   
		fsm_msg_m0_q         <= fsm_msg_m0_next;
		fsm_msg_m0_overlap_q <= fsm_msg_m0_overlap_next;
		fsm_msg_m1_q         <= fsm_msg_m1_next;
		fsm_msg_m1_overlap_q <= fsm_msg_m1_overlap_next;
	end
end


// output
assign upd_axis_tready_o = 1'b1; // we are always ready to accept a new packet 


`ifdef FORMAL

logic [7:0] fsm_f;
assign fsm_f = {
	fsm_invalid_q, 
	fsm_header_h0_q, fsm_header_h1_q, fsm_header_h2_msg_q,
	fsm_msg_m0_q, fsm_msg_m0_overlap_q, fsm_msg_m1_q, fsm_msg_m1_overlap_q};

initial begin
	// assume
	a_reset : assume ( ~nreset );
end

always @(posedge clk) begin
	if ( nreset ) begin
		// fsm
		sva_fsm_onehot : assert( $onehot( fsm_f )); 
	end
end
`endif
endmodule
