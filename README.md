# SystemVerilog Assertion
## Description
> A SystemVerilog testbench for simple Timing Generator
## SVA checker
1. Check edge-to-edge distance signal A rising edge to signal B rising edge should have var_witdh #T  
```systemverilog
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

// example: DA_test1 rising edge and falling edge have B_test1 #T of clk
ap_DA_test1_chk : assert property(A2Bpp_edge_var(clk, C_purstb, DA_test1, ~DA_test1, B_test1[3:0], 1'b1 ))
                  DA_test1_chk_pass += 1;
                  else $display("Error, DA_test1_chk fail");
```
2. Check edge distance with absolute time distance, signal A rising to signal B rising have at least min_time timelapse
```systemverilog
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

// example: DA_test1 rising edge and falling edge should have at least 10us distance
ap_DA_test1_chk1 : assert property(A2Bpp_only_min_abs(DA_test1, ~DA_test1, C_purstb, 1'b1, 10us )) // DA_test1 pulse should be larger than 10us
                   DA_test1_chk1_pass += 1;
                   else $display("Error, DA_test1_chk1 fail");
```
3. Glitch Detection, one-bit signal sig transition within 20ns timelapse
```systemverilog
//=========================================================================================
// assert_glitch
//=========================================================================================
realtime duration = 20ns;
property glitch_p(sig, rstb, special_case);
    realtime first_change;
    @(sig)
    disable iff((rstb & special_case)!= 1'b1)
    (1, first_change = $realtime) |=> (($realtime - first_change) >= duration);
endproperty

// example: Bit0 of DA_test4 have transition within 20ns -> glitch detect
ap_glitch_DA_test4_0: assert property(glitch_p(DA_test4[0], C_purstb, 1'b1 ))
                  DA_test4_0_chk_pass += 1;
                  else $display("Error, DA_test4_0_chk fail");
```
4. Signal check, check signal @ certain state such as POR, ATPG, SUSPEND
> when check_event transition(rstb, atpg, susp) wait strobe time(CHK_STROB), latch signals to be check, then use concurrent assertion to check latch value match answer
```systemverilog
//=======================================================================================
//  assert_ADinterface                                                                   
//=======================================================================================
always@(rstb) 
begin
    #(CHK_STROB);
    if(!rstb && !atpg)
    begin
        por_chk = 1'b1;
        $display("[ASSERT] POR check @ %t", $realtime);
        DA_test1_por_val                =  DA_test1; 

        ap_chk_por_DA_test1:            assert(DA_test1_por_val == DA_test1_por_ans)
                                        else   $display("[ASSERT] Error @ %t, POR check DA_test1", $realtime);

    end
end

always@(atpg)
begin
    #(CHK_STROB);
    if(atpg && rstb)
    begin
        atpg_chk = 1'b1;
        $display("[ASSERT] ATPG check @ %t", $realtime);
        DA_test1_atpg_val               =  DA_test1; 

        ap_chk_atpg_DA_test1:           assert(DA_test1_atpg_val == DA_test1_atpg_ans)
                                        else   $display("[ASSERT] Error @ %t, ATPG check DA_test1", $realtime);

    end
end

always@(susp)
begin
    #(CHK_STROB);
    if(susp && ~atpg)
    begin
        susp_chk = 1'b1;
        $display("[ASSERT] Suspend check @ %t", $realtime);
        DA_test1_susp_val               =  DA_test1; 

        ap_chk_susp_DA_test1:           assert(DA_test1_susp_val == DA_test1_susp_ans)
                                        else   $display("[ASSERT] Error @ %t, Suspend check DA_test1", $realtime);

    end
end


```
## SVA summary report
1. Testbench structure, TestPatterns are inside TB, SVA checkers are inside assert_checker_xx.v
```
TB
--- `include ModeDef.v
--- `include assert_checker_xx.v
--- TestPattern
--- $finish
```
2. Final trigger assert_check_xx.v final procedure block to print log
``` systemverilog
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
```
