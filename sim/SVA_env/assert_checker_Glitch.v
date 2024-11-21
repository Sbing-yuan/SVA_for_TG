module assert_checker_Glitch (
    input [3:0]     DA_test4,
    input           C_purstb     
);

integer DA_test4_0_chk_pass;
integer DA_test4_1_chk_pass;
integer DA_test4_2_chk_pass;
integer DA_test4_3_chk_pass;
initial begin
    DA_test4_0_chk_pass = 0;
    DA_test4_1_chk_pass = 0;
    DA_test4_2_chk_pass = 0;
    DA_test4_3_chk_pass = 0;
end

//=========================================================================================
// assert_glitch
//=========================================================================================
realtime duration = 20ns;                                                                
property glitch_p(sig, rstb, special_case);                                              
    realtime first_change;                                                               
    @(sig)                                                                               
    disable iff((rstb & special_case) != 1'b1)                                           
    (1, first_change = $realtime) |=> (($realtime - first_change) >= duration);          
endproperty 

//=========================================================================================
// assert property below
//=========================================================================================
ap_glitch_DA_test4_0: assert property(glitch_p(DA_test4[0], C_purstb, 1'b1 ))  
                  DA_test4_0_chk_pass += 1;
                  else $display("Error, DA_test4_0_chk fail");

ap_glitch_DA_test4_1: assert property(glitch_p(DA_test4[1], C_purstb, 1'b1 ))  
                  DA_test4_1_chk_pass += 1;
                  else $display("Error, DA_test4_1_chk fail");

ap_glitch_DA_test4_2: assert property(glitch_p(DA_test4[2], C_purstb, 1'b1 ))  
                  DA_test4_2_chk_pass += 1;
                  else $display("Error, DA_test4_2_chk fail");

ap_glitch_DA_test4_3: assert property(glitch_p(DA_test4[3], C_purstb, 1'b1 ))  
                  DA_test4_3_chk_pass += 1;
                  else $display("Error, DA_test4_3_chk fail");

//=========================================================================================
// Assertion Summary 
//=========================================================================================
final
begin
    $display("");
    $display("[ASSERT] Glitch Assertion Summary");
    $display("[ASSERT] DA_test4_0_chk_pass : %d", DA_test4_0_chk_pass);
    $display("[ASSERT] DA_test4_1_chk_pass : %d", DA_test4_1_chk_pass);
    $display("[ASSERT] DA_test4_2_chk_pass : %d", DA_test4_2_chk_pass);
    $display("[ASSERT] DA_test4_3_chk_pass : %d", DA_test4_3_chk_pass);
end

endmodule
