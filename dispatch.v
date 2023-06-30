/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties. */ 

/* Data dispatcher */
module dispatch #(
	parameter AXI_DATA_W = 64,
	parameter AXI_KEEP_W = (AXI_DATA_W/8),
	parameter KEEP_LW    = 3,//$clog2(AXI_KEEP_W + 1),

	parameter LEN_W      = 16,// length field

	// overlap fields
	parameter OV_DATA_W  = 64-LEN_W,//48
	parameter OV_KEEP_W  = (OV_DATA_W/8),//6
	parameter OV_KEEP_LW = 3,//$clog2(OV_KEEP_W+1),


	parameter HEADER_DATA_OFF = 6

)(
	input clk,
	input nreset,

	input                  valid_i,
	input [AXI_DATA_W-1:0] data_i,
	input [AXI_KEEP_W-1:0] keep_i,
	input                  init_v_i,
	input                  last_i,

	output                 msg_end_v_o,

	output                  valid_o,
	output                  start_o,
	output [AXI_DATA_W-1:0] data_o,
	output [KEEP_LW-1:0]    len_o,

	output                  ov_valid_o,
	output                  ov_start_o,
	output [OV_DATA_W-1:0]  ov_data_o,
	output [OV_KEEP_LW-1:0] ov_len_o
);
localparam SEL_DATA_SHIFT_MAX = LEN_W/8;
localparam HEADER_DATA_LEN    = AXI_KEEP_W - HEADER_DATA_OFF; 
// transmitted bytes

// fsm
logic fsm_invalid_next;
logic fsm_msg_next;
logic fsm_len_align_next;
logic fsm_len_split_next;
reg   fsm_invalid_q;
reg   fsm_msg_q;
reg   fsm_len_align_q;
reg   fsm_len_split_q;

// primary pipe logic
logic               sel_msg_end;
logic [LEN_W-1:0]   sel_msg_len_q;
logic [LEN_W-1:0]   sel_msg_len_dec;
logic [LEN_W-1:0]   sel_msg_len_next;
logic [KEEP_LW-1:0] data_len;

// recieved data length
assign data_len = sel_msg_end ? sel_msg_len_q : 
				( valid_i & init_v_i )? HEADER_DATA_LEN :  AXI_KEEP_W; 
assign sel_msg_end = ~sel_msg_len_q[LEN_W-1:KEEP_LW] & ( sel_msg_len_q[KEEP_LW-1:0] <= AXI_KEEP_W ) & ~init_v_i;
assign sel_msg_len_dec = sel_msg_len_q - data_len;
// check if msg end overlaps with the same pl with the begining of the
// next message.
// When this happens start streaming the beging of the next message into the
// other pipe and toggle primary pipe selector
// number of overlap bytes
logic               pload_overlap_v;
logic [KEEP_LW-1:0] pload_overlap_len;
logic [KEEP_LW-1:0] msg_overlap_len;
logic [KEEP_LW-1:0] sel_len_inc2;
logic               sel_len_inc2_overflow;
logic               msg_len_split;
logic               msg_len_align;
logic               msg_len_align_end;
logic               msg_len_inner;

assign pload_overlap_v   = valid_i & msg_len_inner & sel_msg_end & ~fsm_len_align_q & ~(msg_len_split|fsm_len_split_q);
assign pload_overlap_len = data_len - sel_msg_len_q[KEEP_LW-1:0];

assign { sel_len_inc2_overflow , sel_len_inc2 } = sel_msg_len_q[KEEP_LW-1:0] + 'd2;
assign msg_overlap_len   = AXI_KEEP_W - sel_len_inc2;

assign msg_len_split = sel_msg_len_q == 'd7; // only 1 bytes of the length gotten
assign msg_len_align = sel_msg_len_q == 'd8; // no bytes gotten
assign msg_len_inner =( AXI_KEEP_W > sel_msg_len_q[KEEP_LW-1:0] ) & ~msg_len_align_end; // full length available
 
assign msg_len_align_end = ( AXI_KEEP_W == sel_len_inc2 ) & ~sel_len_inc2_overflow; // no bytes gotten
// init new message length
logic               init_len_v;
logic [LEN_W-1:0]   init_len;
logic [LEN_W-1:0]   init_overlap_len;
logic [LEN_W-1:0]   header_msg_len;
logic [7:0]         init_len_p1;
logic [7:0]         init_len_split_half_next;
logic [7:0]         init_len_split_half_q;
logic [7:0]         init_len_p0;

assign init_len_v = valid_i & ( sel_msg_end | init_v_i | fsm_len_split_q );

assign init_len   = {LEN_W{init_v_i}}  & ( { data_i[39:32] , data_i[47:40] } - 'd2 )
				  | {LEN_W{fsm_msg_q & msg_len_align_end}} & { data_i[55:48], data_i[63:56] }
				  | {LEN_W{fsm_msg_q & pload_overlap_v  }} & init_overlap_len
				  | {LEN_W{fsm_len_align_q }} & ({ data_i[7:0], data_i[15:8] } -'d6)
				  | {LEN_W{fsm_len_split_q }} & ({ init_len_split_half_q, data_i[7:0]} - 'd7);

assign init_overlap_len = { init_len_p1, init_len_p0 } -{ {LEN_W-KEEP_LW{1'b0}} , {KEEP_LW{pload_overlap_v}} &  msg_overlap_len };

assign sel_msg_len_next = init_len_v ? init_len : 
						 sel_msg_end ? 'd0 : ( sel_msg_len_q - 'd8 );
always @(posedge clk) begin
	if ( ~nreset ) begin
		sel_msg_len_q <= '0;
	end else begin
		sel_msg_len_q <= sel_msg_len_next;
	end
end
// get length bytes
// will discard shift indexes covered by fsm states:
//  0 : align
//  1 : split
//  KEEP_W-1 : split
logic [KEEP_LW-1:0] len_shift;
logic [LEN_W-1:0]  len_shifted_arr[AXI_KEEP_W-2:2];
logic [LEN_W-1:0]  len_shifted;

assign len_shift = sel_msg_len_q[KEEP_LW-1:0];
genvar s;
generate
for ( s = 2; s < AXI_KEEP_W-1; s++ ) begin
	assign len_shifted_arr[s] = data_i[s*8 + LEN_W-1: s*8];
end
endgenerate
always_comb begin
	for(int i=2; i< AXI_KEEP_W-1; i++) begin
		if( len_shift == i ) len_shifted = len_shifted_arr[i]; 
	end
end
assign init_len_p0 = len_shifted[15:8];
assign init_len_p1 = len_shifted[7:0];

assign init_len_split_half_next = data_i[AXI_DATA_W-1:AXI_DATA_W-8];
always @(posedge clk) begin
	init_len_split_half_q <= init_len_split_half_next;
end

// data len and mask 
logic [KEEP_LW-1:0]    sel_data_len;
logic [KEEP_LW-1:0]    sel_data_len_start;
logic [KEEP_LW-1:0]    ov_data_len;

// working under the assumption that msg len >= 7
assign sel_data_len_start = {KEEP_LW{fsm_len_split_q}} & 'd7
					      | {KEEP_LW{fsm_len_align_q}} & 'd6
					      | {KEEP_LW{fsm_msg_q}} & AXI_KEEP_W
					      | {KEEP_LW{valid_i & init_v_i}} & 'd2;  
assign sel_data_len = ( fsm_msg_q & sel_msg_end) ? sel_msg_len_q : sel_data_len_start;
assign ov_data_len = msg_overlap_len;

// doubling shifting logic to save a on additional logic depth, could share mux logic
// between sel and ov data.
// ov data shift : select ov message data in case of partial presence on payload
// sel data shift : shift to compensate for the presence of length bytes at the begining of
// the payload
logic [KEEP_LW-1:0]    sel_data_shift;
logic [KEEP_LW-1:0]    ov_data_shift;
logic [AXI_DATA_W-1:0] sel_data_shifted; 
logic [AXI_DATA_W-1:0] ov_data_shifted; 
logic [AXI_DATA_W-1:0] data_shifted_arr[AXI_KEEP_W-1:0]; 

// shift of 0 for other cases
assign sel_data_shift = {KEEP_LW{fsm_len_split_q}} & 'd1
					  | {KEEP_LW{fsm_len_align_q}} & 'd2
					  | {KEEP_LW{valid_i & init_v_i}} & HEADER_DATA_OFF; 
assign ov_data_shift = sel_len_inc2;

generate
for ( s = 0; s < AXI_KEEP_W; s++ ) begin
	assign data_shifted_arr[s] = { {s*8{1'bx}} , data_i[AXI_DATA_W-1: 8*s]};
end
endgenerate
always_comb begin
	for(int i=0; i<SEL_DATA_SHIFT_MAX ; i++) begin
		if( sel_data_shift == i ) sel_data_shifted = data_shifted_arr[i];
	end 
	if ( sel_data_shift == HEADER_DATA_OFF ) sel_data_shifted = data_shifted_arr[HEADER_DATA_OFF];
	for(int i=0; i< AXI_KEEP_W; i++) begin
		if( ov_data_shift == i ) ov_data_shifted = data_shifted_arr[i]; 
	end
end
// pipe output valid
logic sel_valid;
logic ov_valid;
assign sel_valid = ( ~fsm_invalid_q | init_v_i ) & valid_i; 
assign ov_valid = ~fsm_invalid_q & pload_overlap_v & valid_i & ~last_i;

// ov msg start
logic sel_data_start;
logic ov_data_start;
assign sel_data_start = fsm_len_split_q | fsm_len_align_q | init_v_i;
assign ov_data_start = 1'b1; // overlap issues allways occure on the start of the packet

// drive output pipes
assign valid_o    = sel_valid;
assign ov_valid_o = ov_valid;
assign start_o    = sel_data_start;
assign ov_start_o = ov_data_start;
assign data_o     = sel_data_shifted;
assign ov_data_o  = ov_data_shifted;
assign len_o      = sel_data_len;
assign ov_len_o   = ov_data_len;

assign msg_end_v_o = sel_msg_end & valid_i;
// FSM
assign fsm_invalid_next = fsm_invalid_q & ~(valid_i& init_v_i) 
						| valid_i & last_i;
assign fsm_msg_next = (( valid_i & init_v_i ) // init
				    | fsm_len_align_q 
					| fsm_len_split_q
					| fsm_msg_q & ~( fsm_len_split_next | fsm_len_align_next)
					) & ~( valid_i & last_i );
assign fsm_len_align_next = fsm_msg_q & sel_msg_end & msg_len_align; 
assign fsm_len_split_next = fsm_msg_q & sel_msg_end & msg_len_split; 

always @(posedge clk) begin
	if ( ~nreset ) begin
		fsm_invalid_q   <= 1'b1;
		fsm_msg_q       <= 1'b0;
		fsm_len_align_q <= 1'b0;
		fsm_len_split_q <= 1'b0;
	end else begin
		fsm_invalid_q   <= fsm_invalid_next;
		fsm_msg_q       <= fsm_msg_next;
		fsm_len_align_q <= fsm_len_align_next;
		fsm_len_split_q <= fsm_len_split_next;
	end
end
`ifdef FORMAL
logic [3:0] f_fsm;
assign f_fsm = { fsm_invalid_q, fsm_msg_q, fsm_len_align_q, fsm_len_split_q };

initial begin
	a_reset : assume( ~nreset );
end
always @(posedge clk) begin
	sva_fsm_onehot : assert( $onehot(f_fsm));

	// xcheck
	xcheck_valid_o : assert( ~$isunknown(valid_o)); 
	xcheck_start_o : assert(~valid_o | valid_o & ~$isunknown(start_o)); 
	xcheck_len_o   : assert(~valid_o | valid_o & ~$isunknown(len_o)); 
	xcheck_ov_valid_o : assert( ~$isunknown(ov_valid_o)); 
	xcheck_ov_start_o : assert(~ov_valid_o | ov_valid_o & ~$isunknown(ov_start_o)); 
	xcheck_ov_len_o   : assert(~ov_valid_o | ov_valid_o & ~$isunknown(ov_len_o)); 	
end
`endif
endmodule
