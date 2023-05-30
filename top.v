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
	parameter AXI_KEEP_W = 8,
	parameter ML_W = 16 // Mold length field width in bits
)(
	input clk,
	input nreset,
	
	// AXI stream interface from udp ethernet
	input                  upd_axis_tvalid_i,
	input [AXI_KEEP_W-1:0] upd_axis_tkeep_i,
	input [AXI_DATA_W-1:0] upd_axis_tdata_i,
	input                  upd_axis_tlast_i,
	input                  upd_axis_tuser_i,
	
	output                 upd_axis_tready_o,

	// Mold message
	output                  mold_msg_v_o,
	output                  mold_msg_start_o, // start of a new msg
	output [ML_W-1:0]       mold_msg_len_o,
	output [AXI_KEEP_W-1:0] mold_msg_mask_o,
	output [AXI_DATA_W-1:0] mold_msg_data_o
);
localparam AXI_MSG_L   = $clog2( AXI_DATA_W / 8 );
localparam AXI_KEEP_LW = $clog2( AXI_KEEP_W ) + 1;
localparam DFF_DATA_W  = AXI_DATA_W - 8; // 56
localparam DFF_DATA_LW = $clog2( DFF_DATA_W ); // 7 
localparam DATA_DIF_W  = AXI_DATA_W - DFF_DATA_W; // 8

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
logic [AXI_KEEP_W-1:0]  msg_end_mask;                  
logic                   msg_overlap;
logic                   cnt_end;


logic                  msg_v;
logic [AXI_DATA_W-1:0] msg_data;

// data routing
// data shifted to be consumed next cycle
logic [DFF_DATA_W-1:0] flop_data_next;
logic [DFF_DATA_W-1:0] flop_data_q;

logic [AXI_KEEP_LW-1:0] flop_shift;
logic [AXI_KEEP_LW-1:0] flop_len_next;
logic [AXI_KEEP_LW-1:0] flop_len_q;

logic [AXI_KEEP_W-1:0] axis_msg_mask;
logic [AXI_KEEP_W-1:0] flop_msg_mask;

logic [AXI_KEEP_LW-1:0] axis_msg_tdata_shift;
logic [AXI_KEEP_LW-1:0] axis_flop_tdata_shift;

// data shifted to be consumed in this cycle
logic [AXI_DATA_W-1:0] axis_msg_tdata_shifted;

logic [AXI_DATA_W-1:0] msg_mask;

// FSM
reg   fsm_invalid_q;
logic fsm_invalid_next;
reg   fsm_h0_q;
reg   fsm_h1_q;
reg   fsm_h2_msg_q;
logic fsm_h0_next;
logic fsm_h1_next;
logic fsm_h2_msg_next;
reg   fsm_msg_q;
reg   fsm_msg_overlap_q;
reg   fsm_msg_len_split_q;
logic fsm_msg_next;
logic fsm_msg_overlap_next;
logic fsm_msg_len_split_next;

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
assign upd_axis_tdata_next  = upd_axis_tdata_i;  
assign upd_axis_tkeep_next  = upd_axis_tkeep_i;
assign upd_axis_tvalid_next = upd_axis_tvalid_i;
assign upd_axis_tlast_next  = upd_axis_tlast_i;
assign upd_axis_tuser_next  = upd_axis_tuser_i;

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
	.h2_v_i(fsm_h2_msg_q),

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

// msg length based on tkeep
cnt_ones_thermo #(.D_W(AXI_KEEP_W),.D_LW(AXI_KEEP_LW))
	m_cnt_ones_tkeep(
	.data_i(upd_axis_tkeep_q),
	.cnt_o(upd_axis_data_len)
);

assign msg_v = fsm_msg_q | fsm_msg_overlap_q | fsm_msg_len_split_q;
// decrement the number of bytes of the current message that have been
// recieved ( ! not sent ) 
assign msg_len_zero = ~|msg_len_q;
assign msg_end      = ~|msg_len_q[ML_W-1:AXI_KEEP_LW] & ( msg_len_q[AXI_KEEP_LW-1:0] <= (AXI_DATA_W/8));

// init msg
assign init_msg_len_sel = { msg_len_zero,   // current message len has reached zero and we are still
					                        // expecting more messages
					        msg_overlap,    // we have an overlap this cycle
						    fsm_h2_msg_q};  // first message
assign init_msg_len_v = fsm_h2_msg_q; 
assign init_msg_len   = { ML_W{ fsm_h2_msg_q }} & ( upd_axis_tdata_q[32+ML_W-1:32] - 'd1);// decrement by the byte of the first packet TODO : support 1st msg len=0
					 /* | { ML_W{ init_msg_len_sel[1] }} & TODO
					  | { ML_W{ init_msg_len_sel[2] }} & ;*/

assign msg_len_next = init_msg_len_v ? init_msg_len :
					  upd_axis_tvalid_q ? msg_len_q - { {ML_W - AXI_KEEP_LW { 1'b0 }}, upd_axis_data_len } :
					  msg_len_q;
always @(posedge clk)
begin
	msg_len_q  <= msg_len_next;
end
// output mask
len_to_mask #(.LEN_W(AXI_KEEP_LW), .LEN_MAX(AXI_KEEP_W)) m_msg_end_mask(
	.len_i(msg_len_q[AXI_KEEP_LW-1:0]),
	.mask_o(msg_end_mask)
);

	
// Message data buffering 
// When possible we want to gather message bits into 64 bits continus chunks

assign flop_len_next = {ML_W{fsm_h1_q}} & {ML_W{1'b0}} // reset flop len to 0
					 | {ML_W{fsm_h2_msg_q}} & 'd2  // TODO : add support for first msg len=0 
					 | {ML_W{fsm_msg_q & ~msg_end }} & flop_len_q; // keep current flop len shift until the end of the message
assign flop_shift  = {ML_W{fsm_h2_msg_q}} & 'd2 
				   | {ML_W{fsm_msg_q}} & flop_len_q; 
 
//assign axis_flop_tdata_shift = flop_len_next; 

//assign axis_msg_tdata_shift = flop_len_next;

// TODO : move declaration to top ?
logic [AXI_DATA_W-1:0] axis_flop_tdata_shifted_arr[DFF_DATA_W-1:0];
logic [AXI_DATA_W-1:0] axis_msg_tdata_shifted_arr[DFF_DATA_W-1:0];
genvar j;
generate
	assign axis_flop_tdata_shifted_arr[0] = {AXI_DATA_W{1'b0}}; 
	assign axis_msg_tdata_shifted_arr[0]  = {AXI_DATA_W{1'b0}}; 
	for( j = 1; j < DFF_DATA_LW; j++) begin
		assign axis_flop_tdata_shifted_arr[j] =	{ { 64-(8*j) {1'b0} }, upd_axis_tdata_q[63:(64-(8*j))] }; 
		assign axis_msg_tdata_shifted_arr[j] = { upd_axis_tdata_q[(63-(8*j)):0], {8*j{1'b0}} };
	end
endgenerate

always_comb begin
	flop_data_next = { AXI_DATA_W{1'bX}}; // default
	axis_msg_tdata_shifted  = { AXI_DATA_W{1'bX}}; // default
	for( int unsigned i=0; i <= DFF_DATA_LW; i++) begin
	 	if (i == flop_shift) flop_data_next = axis_flop_tdata_shifted_arr[i];
	 	if (i == flop_shift) axis_msg_tdata_shifted  = axis_msg_tdata_shifted_arr[i]; 
	end
end

always @(posedge clk) begin
	flop_len_q <= flop_len_next;
	flop_data_q <= flop_data_next;
end


// mask
len_to_mask #(.LEN_W(AXI_KEEP_LW), .LEN_MAX(AXI_KEEP_W)) m_flop_msg_mask(
	.len_i(flop_len_q),
	.mask_o(flop_msg_mask)
);

generate 
	for ( j = 0; j < AXI_KEEP_W; j++) begin
		assign msg_data[j*8+7:j*8] = {8{flop_msg_mask[j]}} & flop_data_q[j*8+7:j*8]
								   | {8{~flop_msg_mask[j]}} & axis_msg_tdata_shifted[j*8+7:j*8];
	end
endgenerate

// decrement the number of messages we are still expected to see if we have
// reaced the end of the current message
assign msg_cnt_next = init_msg_cnt_v ? init_msg_cnt :
					  msg_end ? msg_cnt_q - { {ML_W-1{1'b0}}, 1'b1 } : msg_cnt_q;
assign cnt_end = ~|msg_cnt_next; 
always @(posedge clk)
begin
	msg_cnt_q <= msg_cnt_next;	
end
// fsm

assign fsm_invalid_next = fsm_invalid_q & ~upd_axis_tvalid_i // first payload received
						| fsm_msg_q & ( msg_end & cnt_end );
// header 
// hX  : header is received over multiple cycles 
// msg : during last cycle part of the packed is the begining of the message
assign fsm_h0_next     = fsm_invalid_q & upd_axis_tvalid_i;
assign fsm_h1_next     = fsm_h0_q;
assign fsm_h2_msg_next = fsm_h1_q; 

// message
// overlap : part of the next axi payload is of a different modlupd64 message
//           it will be routed to the free moldupd64 module
assign fsm_msg_next = fsm_h2_msg_q 
					| fsm_msg_q & ~(msg_end & cnt_end);


// TODO : unused fsm states for now
assign fsm_msg_overlap_next   = 1'b0;  
assign fsm_msg_len_split_next = 1'b0;
always @(posedge clk)
begin
	if ( ~nreset ) begin
		fsm_invalid_q    <= 1'b1;
		fsm_h0_q         <= 1'b0;
		fsm_h1_q         <= 1'b0;
		fsm_h2_msg_q     <= 1'b0;
		fsm_msg_q         <= 1'b0;
		fsm_msg_overlap_q <= 1'b0;
		fsm_msg_len_split_q <= 1'b0;
		end else begin
		fsm_invalid_q    <= fsm_invalid_next; 
		fsm_h0_q         <= fsm_h0_next;     
		fsm_h1_q         <= fsm_h1_next;    
		fsm_h2_msg_q     <= fsm_h2_msg_next;   
		fsm_msg_q         <= fsm_msg_next;
		fsm_msg_overlap_q   <= fsm_msg_overlap_next;
		fsm_msg_len_split_q <= fsm_msg_len_split_next;
	end
end


// output
assign upd_axis_tready_o = 1'b1; // we are always ready to accept a new packet 

assign mold_msg_v_o    = msg_v; 
assign mold_msg_data_o = msg_data; 
assign mold_msg_mask_o = msg_end ? msg_end_mask : '1; 

`ifdef FORMAL

logic [0:6] fsm_f;
assign fsm_f = {
	fsm_invalid_q, 
	fsm_h0_q, fsm_h1_q, fsm_h2_msg_q,
	fsm_msg_q, fsm_msg_overlap_q, fsm_msg_len_split_q};

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
