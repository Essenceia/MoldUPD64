/* Generic endianness conversion modules
*
* These modules only support types with a single grandule
* aka : not pairs, eg : long pair
*/ 

/* Big endian to little endian */
module endian_flip #(
	parameter B = 8// number of bytes
)(
	input logic  [8*B-1:0] d_i,
	output logic [8*B-1:0] d_o
);

genvar i;
generate
	for( i=0; i < B; i++) begin
		assign d_o[8*i+7:8*i] = d_i[8*(B-i-1)+7:8*(B-i-1)];
	end
endgenerate
`ifdef FORMAL

always_comb 
begin
	sva_not_unknown : assert( $isunknown(d_i) | ( ~$isunknown(d_i) & ~$isunknown(d_o)));

	for( int x=0; x<B; x++) begin
		assert( d_i[8*x+7:8*x] == d_o[8*(B-x-1)+7:8*(B-x-1)] );
	end
end

`endif //FORMAL
endmodule
