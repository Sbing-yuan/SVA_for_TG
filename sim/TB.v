`timescale 1ns/1ps
`define VCDDUMP

module TB();

initial begin
    #(200000);
    $finish;
end

DUT U1(
/*AUTOINST*/
       // Inouts
       .SDA				(SDA),
       .SCL				(SCL));

`ifdef VCDDUMP
initial begin
    $dumpfile("Test.vcd");  //
    $dumpvars(0,TB);       
end
`endif

endmodule

