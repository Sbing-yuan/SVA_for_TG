module DUT(
    SDA, SCL
);

inout SDA;
inout SCL;

reg pu_sig;
reg clk;
reg clk_lp;

initial begin
    pu_sig  = 1'b0;
    clk     = 1'b0;
    clk_lp  = 1'b0;
    #2000;
    pu_sig  = 1'b1;
end

always #10  clk    = ~clk;
always #133 clk_lp = ~clk_lp;

my_design U1(
         // Inputs
         .pu_sig            (pu_sig),
         .clk               (clk),
         .clk_lp            (clk_lp));

endmodule
