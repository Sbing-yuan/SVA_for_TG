TB:
	iverilog TB.v -o TB.o -y ../rtl
	vvp TB.o
	rm TB.o	

GTK:
	export DISPLAY=:0

VM:
	xemacs --batch $(file) -f verilog-auto-save-compile

