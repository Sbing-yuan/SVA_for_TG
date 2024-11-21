module assert_checker_PMU (
    input           DA_test1,
    input           DA_test2,
    input           DA_test3,
    input [3:0]     DA_test4,
    input           C_purstb     
);

integer DA_test1_chk1_pass;
integer DA_test1_chk2_pass;
integer DA_test23_chk_pass;
initial begin
    DA_test1_chk1_pass = 0;
    DA_test1_chk2_pass = 0;
    DA_test23_chk_pass = 0;
end

// check A rising edge to B rising edge > min_time
//=========================================================================================
// assert_only_edge_absolute
//=========================================================================================
property A2Bpp_only_min_abs(A, B, rstb, special_case, min_time);
    realtime a_time;
    @(posedge A)
    disable iff((rstb & special_case) != 1'b1)
    (1, a_time = $realtime) |-> @(posedge B) ($realtime - a_time > min_time)
endproperty

// check A rising edge to B rising edge > min_time, within settling time B should be low
//=========================================================================================
// assert_edge_absolute
//=========================================================================================
property A2Bpp_min_abs(A, B, rstb, special_case, min_time);
    realtime a_time;
    @(posedge A)
    disable iff((rstb & special_case) != 1'b1)
    (1, a_time = $realtime) |-> ~B ##0 @(posedge B) ($realtime - a_time > min_time)
endproperty

//=========================================================================================
// assert property below
//=========================================================================================
ap_DA_test1_chk1 : assert property(A2Bpp_only_min_abs(DA_test1, ~DA_test1, C_purstb, 1'b1, 10us )) // DA_test1 pulse should be larger than 10us
                   DA_test1_chk1_pass += 1;
                   else $display("Error, DA_test1_chk1 fail");

ap_DA_test1_chk2 : assert property(A2Bpp_min_abs(DA_test1, ~DA_test1, C_purstb, 1'b1, 10us ))      // DA_test1 pulse should be larger than 10us
                   DA_test1_chk2_pass += 1;
                   else $display("Error, DA_test1_chk2 fail");

ap_DA_test23_chk : assert property(A2Bpp_min_abs(DA_test2, ~DA_test3, C_purstb, 1'b1, 20ns ))      // DA_test2 rise to DA_test3 fall should be larger than 20ns
                   DA_test23_chk_pass += 1;
                   else $display("Error, DA_test23_chk fail");

//=========================================================================================
// Assertion Summary 
//=========================================================================================
final
begin
    $display("");
    $display("[ASSERT] PMU Assertion Summary");
    $display("[ASSERT] DA_test1_chk1_pass : %d", DA_test1_chk1_pass);
    $display("[ASSERT] DA_test1_chk2_pass : %d", DA_test1_chk2_pass);
    $display("[ASSERT] DA_test23_chk_pass : %d", DA_test23_chk_pass);
end

endmodule
