module assert_checker_TG (
    input           DA_test1,
    input           DA_test2,
    input           DA_test3,
    input [3:0]     DA_test4,
    input           clk,         
    input [3:0]     B_test1,     
    input [3:0]     B_test2,     
    input [3:0]     B_test3,     
    input           C_purstb     
);

integer DA_test1_chk_pass;
integer DA_test2_chk_pass;
integer DA_test3_chk_pass;
initial begin
    DA_test1_chk_pass = 0;
    DA_test2_chk_pass = 0;
    DA_test3_chk_pass = 0;
end

//=========================================================================================
// assert_edge_variable
//=========================================================================================
property A2Bpp_edge_var(clk, rstb, A, B, var_width, special_case);
    @(posedge clk)
    disable iff((rstb & special_case) != 1'b1)
    $rose(A) |-> delay_seq(var_width) |-> $rose(B);
endproperty

sequence delay_seq(v_width);
    int width;
    (1, width = v_width) ##0 first_match((1, width=width - 1) [*0:$] ##0 width < 0);
endsequence

//=========================================================================================
// assert property below
//=========================================================================================
ap_DA_test1_chk : assert property(A2Bpp_edge_var(clk, C_purstb, DA_test1, ~DA_test1, B_test1[3:0], 1'b1 ))  
                  DA_test1_chk_pass += 1;
                  else $display("Error, DA_test1_chk fail");

ap_DA_test2_chk : assert property(A2Bpp_edge_var(clk, C_purstb, DA_test1, DA_test2, 1, 1'b1 ))  
                  DA_test2_chk_pass += 1;
                  else $display("Error, DA_test2_chk fail");

ap_DA_test3_chk : assert property(A2Bpp_edge_var(clk, C_purstb, DA_test1, DA_test3, 1, 1'b1 ))  
                  DA_test3_chk_pass += 1;
                  else $display("Error, DA_test3_chk fail");

//=========================================================================================
// Assertion Summary 
//=========================================================================================
final
begin
    $display("");
    $display("[ASSERT] TG Assertion Summary");
    $display("[ASSERT] DA_test1_chk : %d", DA_test1_chk_pass);
    $display("[ASSERT] DA_test2_chk : %d", DA_test2_chk_pass);
    $display("[ASSERT] DA_test3_chk : %d", DA_test3_chk_pass);
end

endmodule
