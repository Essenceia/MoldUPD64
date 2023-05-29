TB_DIR=tb
BUILD=build
FLAGS=-g2012

all: top run

cnt_ones_thermo : cnt_ones_thermo.v
	iverilog ${FLAGS} -s cnt_ones_thermo -o ${BUILD}/cnt_ones_thermo cnt_ones_thermo.v

header: header.v
	iverilog ${FLAGS} -s header -o ${BUILD}/header header.v

top: top.v header.v ${TB_DIR}/top_test.v
	iverilog ${FLAGS} -s top_test -o ${BUILD}/top cnt_ones_thermo.v header.v top.v ${TB_DIR}/top_test.v

run:
	vvp ${BUILD}/top
