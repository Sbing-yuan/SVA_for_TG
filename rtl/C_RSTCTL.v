module C_RSTCTL(/*AUTOARG*/
   // Outputs
   rstb_out,
   // Inputs
   rstb_in, clk_lp, clk
   );

output  rstb_out;
input   rstb_in;
input   clk_lp;
input   clk;

reg [7:0] rstcnt;
reg       rstb_reg;

always@(posedge clk_lp or negedge rstb_in)
begin
    if(~rstb_in)
    begin
        rstcnt <= 8'd0;
        rstb_reg <= 1'b0;
    end
    else
    begin
        if(rstcnt <= 8'd128)
            rstcnt <= rstcnt + 8'd1;  
        else
            rstb_reg <= 1'b1;
    end
end


CDCSync_Signal_ResetL rstb_reg_sync(
                  // Outputs
                  .DO           (rstb_out),
                  // Inputs
                  .clk          (clk),
                  .rst_n        (rstb_reg),
                  .DI           (1'b1)
);

endmodule
