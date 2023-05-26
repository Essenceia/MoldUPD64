// ModlUPD64 receiver
module receiver #(
	parameter P_W = 800, // packed width
	parameter OP_W  = 255, // output packed width 
	parameter OP_LW = 8,   // output packed widht log2 
	parameter MSG_W  = 512, // max message lenght
	parameter MSG_LW = 9,   // max message lenght log2
)(
	input clk,
	input nreset,
	
	// AXI stream interface from udp ethernet
	input        upd_axis_tvalid_i,
	output       upd_axis_tready_i,
 
	input [63:0] upd_axis_tdata_i,
	input [7:0]  upd_axis_tkeep_i,
	input        upd_axis_tlast_i,
	input        upd_axis_tuser_i,
	
	
);

/* Receiver fsm : tracks what part of the packet we are receiving on the
 * axi streaming interface. */
reg fsm_invalid_q;
reg fsm_header_q;
reg fsm_header_q;

endmodule
