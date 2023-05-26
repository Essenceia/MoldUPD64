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

// FSM
reg  fsm_invalid_q;
wire fsm_invalid_next;
// header 
// hX  : header is received over multiple cycles 
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

// AXI 
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

// axi payload buffering ( for timing, might replace with clk domain crossing )
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
// Header
header m_header(
	.data_i(upd_axis_tdata_q),
	.h0_v_i(fsm_header_h0_q),
	.h1_v_i(fsm_header_h1_q),
	.h1_v_i(fsm_header_h2_msg_q),

	.sid_p0_v_o(), 
	.sid_p0_o(),
	.sid_p1_v_o(),
	.sid_p1_o(),
	.seq_num_p0_v_o(),
	.seq_num_p0_o(),
	.seq_num_p1_v_o(),
	.seq_num_p1_o(),
	.msg_cnt_v_o(),
	.msg_cnt_o ()

);


// fsm



assign fsm_header_h0_next     = fsm_invalid_q & upd_axis_tvalid_i;
assign fsm_header_h1_next     = fsm_header_h0_q;
assign fsm_header_h2_msg_next = fsm_header_h1_q; 

assign fsm_msg_m0_next = fsm_header_h2_msg_q; // default state
 
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
		// assume
		// AXI valid is never X
		a_axi_tvalid_know : assume ( ~$isunknown( upd_axis_tvalid_i ));
		// AXI doesn't drive X's when valid
		a_axi_valid_tdata_known : assume( upd_axis_tvalid_i | ( upd_axis_tvalid_i &  ~$isunknown( upd_axis_tdata_i )));
		a_axi_valid_tkeep_known : assume( upd_axis_tvalid_i | ( upd_axis_tvalid_i &  ~$isunknown( upd_axis_tkeep_i )));
		a_axi_valid_tlast_known : assume( upd_axis_tvalid_i | ( upd_axis_tvalid_i &  ~$isunknown( upd_axis_tlast_i )));
		a_axi_valid_tuser_known : assume( upd_axis_tvalid_i | ( upd_axis_tvalid_i &  ~$isunknown( upd_axis_tuser_i )));
		// fsm
		sva_fsm_onehot : assert( $onehot( fsm_f )); 
	end
end
`endif
endmodule
