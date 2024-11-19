module my_design(
/*AUTOARG*/
   // Inputs
   pu_sig, clk, clk_lp
   );

input pu_sig;
input clk;
input clk_lp;

/*AUTOWIRE*/
// Beginning of automatic wires (for undeclared instantiated-module outputs)
wire            DA_test1;       // From U_TG of TimingGen.v
wire            DA_test2;       // From U_TG of TimingGen.v
wire            DA_test3;       // From U_TG of TimingGen.v
wire [3:0]      DA_test4;       // From U_TG of TimingGen.v
// End of automatics


wire [3:0]  B_test1 = 4'd5;
wire [3:0]  B_test2 = 4'd7;
wire [3:0]  B_test3 = 4'd9;

CDCSync_Signal_ResetL pu_sig_sync(
                  // Outputs
                  .DO           (pu_sig_sync),
                  // Inputs
                  .clk          (clk),
                  .rst_n        (pu_sig),
                  .DI           (1'b1)
);

C_RSTCTL UC_RSTCTL(
                  // Outputs
                  .rstb_out     (C_purstb),
                  // Inputs
                  .clk          (clk),
                  .clk_lp       (clk_lp),
                  .rstb_in      (pu_sig_sync) 
);

TimingGen U_TG(
           // Outputs
           .DA_test1        (DA_test1),
           .DA_test2        (DA_test2),
           .DA_test3        (DA_test3),
           .DA_test4        (DA_test4[3:0]),
           // Inputs
           .clk             (clk),
           .B_test1         (B_test1[3:0]),
           .B_test2         (B_test2[3:0]),
           .B_test3         (B_test3[3:0]),
           .C_purstb        (C_purstb));

endmodule
