TB_DIR=tb
BUILD=build

all: build run

build:
	iverilog -o ${BUILD}/top ${TB_DIR}/top_test.v

run:
	vvp ${BUILD}/top
