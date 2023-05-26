/* Module is a slave connected to an AXI steam interface */

module top #(
	parameter AXI_DATA_W = 64,
	parameter AXI_KEEP_W = 8,// $clog2(AXI_DATA_W)
	parameter ML_W = 16 // Mold length field width in bits
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
// metadata
reg   [ML_W-1:0] msg_cnt_q;
logic [ML_W-1:0] msg_cnt_next;
logic            init_msg_cnt_v;
logic [ML_W-1:0] init_msg_cnt;
reg   [ML_W-1:0] msg_len_q;
logic [ML_W-1:0] msg_len_next;
logic [ML_W-1:0] init_msg_len;
logic            init_msg_len_v;
logic        msg_end;
logic        seq_last;
// FSM
reg   fsm_invalid_q;
logic fsm_invalid_next;
reg   fsm_h0_q;
reg   fsm_h1_q;
reg   fsm_h2_msg_q;
logic fsm_h0_next;
logic fsm_h1_next;
logic fsm_h2_msg_next;
reg   fsm_m0_q;
reg   fsm_m0_overlap_q;
reg   fsm_m1_q;
reg   fsm_m1_overlap_q;
logic fsm_m0_next;
logic fsm_m0_overlap_next;
logic fsm_m1_next;
logic fsm_m1_overlap_next;

// AXI 
reg [AXI_DATA_W-1:0]   upd_axis_tdata_q;
reg [AXI_KEEP_W-1:0]   upd_axis_tkeep_q;
reg                    upd_axis_tvalid_q;
reg                    upd_axis_tlast_q;
reg                    upd_axis_tuser_q;
logic [AXI_DATA_W-1:0] upd_axis_tdata_next;
logic [AXI_KEEP_W-1:0] upd_axis_tkeep_next;
logic                  upd_axis_tvalid_next;
logic                  upd_axis_tlast_next;
logic                  upd_axis_tuser_next;

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
 
// Header
header m_header(
	.data_i(upd_axis_tdata_q),
	.h0_v_i(fsm_h0_q),
	.h1_v_i(fsm_h1_q),
	.h1_v_i(fsm_h2_msg_q),

	.sid_p0_v_o(), 
	.sid_p0_o(),
	.sid_p1_v_o(),
	.sid_p1_o(),
	.seq_num_p0_v_o(),
	.seq_num_p0_o(),
	.seq_num_p1_v_o(),
	.seq_num_p1_o(),
	.msg_cnt_v_o(init_msg_cnt_v),
	.msg_cnt_o (init_msg_cnt)

);
// message and sequence tracking
// decrement the number of bytes of the current message that have been
// recieved
// decrement the number of messages we are still expected to see if we have
// reaced the end of the current message
assign msg_cnt_next = init_msg_cnt_v ? init_msg_cnt :
						msg_end ? msg_cnt_q - ML_W'd1 : msg_cnt_q;

always @(posedge clk)
begin
	msg_cnt_q <= msg_cnt_next;	
end
// fsm

// header 
// hX  : header is received over multiple cycles 
// msg : during last cycle part of the packed is the begining of the message
assign fsm_h0_next     = fsm_invalid_q & upd_axis_tvalid_i;
assign fsm_h1_next     = fsm_h0_q;
assign fsm_h2_msg_next = fsm_h1_q; 

// message
// message can be sent over multiple message modules m0 and m1
// mX      : denotes the module to which the start of the axi stream payload
//           will be sent, default is m0
// overlap : part of the next axi payload is of a different modlupd64 message
//           it will be routed to the free moldupd64 module
assign fsm_m0_next = fsm_h2_msg_q;
 
always @(posedge clk)
begin
	if ( ~nreset ) begin
		fsm_invalid_q    <= 1'b1;
		fsm_h0_q         <= 1'b0;
		fsm_h1_q         <= 1'b0;
		fsm_h2_msg_q     <= 1'b0;
		fsm_m0_q         <= 1'b0;
		fsm_m0_overlap_q <= 1'b0;
		fsm_m1_q         <= 1'b0;
		fsm_m1_overlap_q <= 1'b0;	
		end else begin
		fsm_invalid_q    <= fsm_invalid_next; 
		fsm_h0_q         <= fsm_h0_next;     
		fsm_h1_q         <= fsm_h1_next;    
		fsm_h2_msg_q     <= fsm_h2_msg_next;   
		fsm_m0_q         <= fsm_m0_next;
		fsm_m0_overlap_q <= fsm_m0_overlap_next;
		fsm_m1_q         <= fsm_m1_next;
		fsm_m1_overlap_q <= fsm_m1_overlap_next;
	end
end


// output
assign upd_axis_tready_o = 1'b1; // we are always ready to accept a new packet 


`ifdef FORMAL

logic [0:7] fsm_f;
assign fsm_f = {
	fsm_invalid_q, 
	fsm_h0_q, fsm_h1_q, fsm_h2_msg_q,
	fsm_m0_q, fsm_m0_overlap_q, fsm_m1_q, fsm_m1_overlap_q};

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
		
		// msg cnt init should happen when we receive the last part of the
		// header
		sva_msg_cnt_init_h2 : assert ( init_msg_cnt_v == fsm_h2_msg_q);
		sva_xcheck_msg_cnt : assert ( ~|fsm_f[7:4] | ( |fsm_f[7:4] & ~$isunknown( msg_cnt_q )));
	end
end
`endif
endmodule
