/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties.
 * 
 * For purchasing a commertial license contact : julia.desmazes@gmail.com  */ 


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
localparam AXI_MSG_L   = $clog2( AXI_DATA_W / 8 );
localparam AXI_KEEP_LW = $clog2( AXI_KEEP_W ) + 1;

// metadata
reg   [ML_W-1:0] msg_cnt_q;
logic [ML_W-1:0] msg_cnt_next;
logic            init_msg_cnt_v;
logic [ML_W-1:0] init_msg_cnt;
reg   [ML_W-1:0] msg_len_q;
logic [ML_W-1:0] msg_len_next;
logic [ML_W-1:0] init_msg_len;
logic            init_msg_len_v;
logic [2:0]      init_msg_len_sel;

logic [AXI_KEEP_LW-1:0] upd_axis_data_len; 
logic [ML_W-1:0]        msg_len_dec;
logic                   msg_len_zero;
logic                   msg_end;
logic                   msg_overlap;
logic                   cnt_last;

logic                  msg_valid[1:0];
// data routing
logic [AXI_DATA_W-1:0] msg_data [1:0];
logic [AXI_DATA_W-1:0] msg_data_shifted;
logic [AXI_MSG_L-1:0]  msg_shift; // only 1 of the 2 modules if going to call for a shift
logic [AXI_KEEP_W-1:0] msg_mask[1:0];

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

// Data routing
assign msg_valid[0] = fsm_h2_msg_q // first message is routed by default to m0
					| msg_overlap
					| fsm_m0_q; 
assign msg_valid[1] = msg_overlap
					| fsm_m1_q;

assign msg_data[0] = {AXI_DATA_W{fsm_h2_msg_q}} & { 32'b0, upd_axis_tdata_q[63:32]} 
				   | {AXI_DATA_W{fsm_m0_q|fsm_m0_overlap_q}} & upd_axis_tdata_q
				   | {AXI_DATA_W{fsm_m1_overlap_q}} & msg_data_shifted;
assign msg_data[1] = {AXI_DATA_W{fsm_m1_q}} & upd_axis_tdata_q
				   | {AXI_DATA_W{fsm_m1_q|fsm_m1_overlap_q}} & upd_axis_tdata_q
				   | {AXI_DATA_W{fsm_m0_overlap_q}} & msg_data_shifted;

assign msg_mask[0] = {AXI_KEEP_W{fsm_h2_msg_q}} & { 4'b0, upd_axis_tkeep_q[7:0]}
				   | {AXI_KEEP_W{fsm_m0_q}} & upd_axis_tkeep_q
				   | {AXI_KEEP_W{fsm_m0_overlap_q}} & TODO
				   | {AXI_KEEP_W{fsm_m1_overlap_q}} & TODO; 
assign msg_mask[1] = {AXI_KEEP_W{fsm_m1_q}} & upd_axis_tkeep_q
				   | {AXI_KEEP_W{fsm_m0_overlap_q}} & TODO
				   | {AXI_KEEP_W{fsm_m1_overlap_q}} & TODO;

// message and sequence tracking

// msg length based on tkeep
cnt_ones_thermo m_cnt_ones_tkeep#(.D_W(AXI_KEEP_W),.D_LW(AXI_KEEP_LW))(
	.data_i(upd_axis_tkeep_q),
	.cnt_o(upd_axis_data_len)
);

// decrement the number of bytes of the current message that have been
// recieved
assign msg_len_zero = ~|msg_len_q;
assign msg_end      = ( ~|msg_len_q[ML_W-1:AXI_KEEP_LW] & ( msg_len_q[AXI_KEEP_LW-1:0] <= upd_axis_data_len );
assign msg_overlap  = fsm_m1_overlap_q | fsm_m0_overlap_q;

// init msg
assign init_msg_len_sel = { msg_len_zero,   // current message len has reached zero and we are still
					                        // expecting more messages
					        msg_overlap,    // we have an overlap this cycle
						    fsm_h2_msg_q};  // first message
assign init_msg_len_v = |init_msg_len_sel; 
assign init_msg_len   = { ML_W{ init_msg_len_sel[0] }} &  upd_axis_tdata_q[48:32]
					  | { ML_W{ init_msg_len_sel[1] }} & TODO
					  | { ML_W{ init_msg_len_sel[2] }} & ;
 
assign msg_len_next = init_msg_len_v ? init_msg_len :
					  upd_axis_tvalid_q ? msg_len_q - { {ML_W - AXI_KEEP_LW { 1'b0 }}, upd_axis_data_len } :
					  msg_len_q;
	
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
		a_axi_valid_tdata_known : assume( ~upd_axis_tvalid_i | ( upd_axis_tvalid_i &  ~$isunknown( upd_axis_tdata_i )));
		a_axi_valid_tkeep_known : assume( ~upd_axis_tvalid_i | ( upd_axis_tvalid_i &  ~$isunknown( upd_axis_tkeep_i )));
		a_axi_valid_tlast_known : assume( ~upd_axis_tvalid_i | ( upd_axis_tvalid_i &  ~$isunknown( upd_axis_tlast_i )));
		a_axi_valid_tuser_known : assume( ~upd_axis_tvalid_i | ( upd_axis_tvalid_i &  ~$isunknown( upd_axis_tuser_i )));
		// tkeep is a thermometer
		a_axi_tkeep_thermo : assume( ~udp_axis_tvalid_i | ( upd_axis_tvalid_i & $onehot0( upd_axis_tkeep_i - AXI_KEEP_W'd1 ))); 
		// tkeep is only not only 1s on the last payload
		a_axi_tkeep_n1s_only_tlast : assume ( ~upd_axis_tvalid_i | ( upd_axis_tvalid_i & ~upd_axis_tlast_i & &upd_axis_tkeep_i ));
	
		// fsm
		sva_fsm_onehot : assert( $onehot( fsm_f )); 
		
		// msg cnt init should happen when we receive the last part of the
		// header
		sva_msg_cnt_init_h2 : assert ( init_msg_cnt_v == fsm_h2_msg_q);
		sva_xcheck_msg_cnt : assert ( ~|fsm_f[7:4] | ( |fsm_f[7:4] & ~$isunknown( msg_cnt_q )));

		// init msg sel should be onehot, used in mux
		sva_init_msg_len_sel_onehot : assert ( ~init_msg_len_v | ( init_msg_len_v & $onehot( init_msg_len_sel )));
	end
end
`endif
endmodule
