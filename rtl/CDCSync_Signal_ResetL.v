module CDCSync_Signal_ResetL(
/*AUTOARG*/
   // Outputs
   DO,
   // Inputs
   clk, rst_n, DI
   );

input   clk;
input   rst_n;
input   DI;
output  DO;

reg CDCSync_DI_1P;
reg CDCSync_DI_2P;

always@(posedge clk or negedge rst_n)
begin
    if(~rst_n)
    begin
        CDCSync_DI_1P <= 1'b0;
        CDCSync_DI_2P <= 1'b0;
    end
    else
    begin
        CDCSync_DI_1P <= DI;
        CDCSync_DI_2P <= CDCSync_DI_1P;
    end
end

assign DO = CDCSync_DI_2P;

endmodule
