TB:
	iverilog TB.v -o TB.o -y ./
	vvp TB.o
	rm TB.o	

GTK:
	export DISPLAY=:0
	gtkwave

VM:
	xemacs --batch $(file) -f verilog-auto-save-compile

RM:
	rm *~
