run_ivsim:
	iverilog TB.v -o TB.o -y ../rtl
	vvp TB.o
	rm TB.o	

run_mdsim:
	vlib.exe work
	vlog.exe -sv -timescale "1ns/1ps" TB.v ../rtl/*.v
	vsim.exe -c -L work -voptargs=+acc -do 'run -all' -do 'exit' TB
	rm -rf vsim* work/

run:
	@echo "" > ModeDef.v
	make run_mdsim	

run_TG:
	@echo "\`define ASSERT_TG" > ModeDef.v
	make run_mdsim	

GTK:
	export DISPLAY=:0

VM:
	xemacs --batch $(file) -f verilog-auto-save-compile

