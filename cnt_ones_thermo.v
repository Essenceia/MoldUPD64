// Count the number of 1s in the thermometer data_i
module cnt_ones_thermo #(
	parameter D_W = 8,
	parameter D_LW = 3+1 // clog2( D_W ) + 1
)(
	input  [D_W-1:0]  data_i,
	output [D_LW-1:0] cnt_o
);

logic [D_W:0] data_onehot;
assign data_onehot = data_i + D_W'd1;

always_comb begin
	cnt_o = {D_LW{1'bX}}; //default
	for( int i=0; i <= D_W; i++ ) begin
		if ( data_onehot[i] == 1'b1 ) cnt_o = i;
	end
end


`ifdef FORMAL

logic [D_W:0] data_onehot_f;

assign data_onehot_f = data_i + D_W'd1;
always_comb begin
	// data_i is expected to be a thermometer
	a_data_thermo : assume ( $onehot( data_onehot_f )); 
	sva_cnt : assert ( $countones(data_i) == cnt_o );
end

`endif
endmodule


 
