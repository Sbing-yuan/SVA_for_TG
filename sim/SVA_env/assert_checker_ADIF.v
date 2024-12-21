function string chk_result_log(input NA, input chk_flg, input integer val_read, input integer val_golden);
    if(NA) // no need to check
        chk_result_log = "NA";
    else if(!chk_flg) // should check but no check event
        chk_result_log = "NoE";
    else if(val_read == val_golden) // Pass 
        chk_result_log = $sformatf("%3d", val_read);
    else // Fail
        chk_result_log = $sformatf("%3d(%3d)", val_read, val_golden);
endfunction

module assert_checker_ADIF (
    input           DA_test1,
    input           DA_test2,
    input           DA_test3,
    input [3:0]     DA_test4,
    input           susp, 
    input           atpg, 
    input           rstb 
);


parameter CHK_STROB = 20; //change Strobe time

wire por_chk_event_tmp = !rstb & !atpg;
wire atpg_chk_event_tmp = atpg & rstb;
wire susp_chk_event_tmp = susp & ~atpg;
wire #(CHK_STROB) por_chk_event_tmp_dly = por_chk_event_tmp;
wire #(CHK_STROB) atpg_chk_event_tmp_dly = atpg_chk_event_tmp;
wire #(CHK_STROB) susp_chk_event_tmp_dly = susp_chk_event_tmp;
wire por_chk_event = por_chk_event_tmp & por_chk_event_tmp_dly;
wire atpg_chk_event = atpg_chk_event_tmp & atpg_chk_event_tmp_dly;
wire susp_chk_event = susp_chk_event_tmp & susp_chk_event_tmp_dly;

// xx_chk_event_tmp
//               _______________
//      ________/               \___
// chk_strob ------>
// x: no_chk
// v: chk
// xxxxxxxxxxxxxxxxxvvvvvvvvvvvvxxxxx
    
reg por_chk;
reg atpg_chk;
reg susp_chk;
initial begin
    por_chk   = 1'b0;
    atpg_chk  = 1'b0;
    susp_chk  = 1'b0;
end

//=======================================================================================
//  POR_VAL                                                                              
//=======================================================================================
integer DA_test1_por_val;           parameter DA_test1_por_ans = 1;
integer DA_test2_por_val;           parameter DA_test2_por_ans = 0;
integer DA_test3_por_val;           parameter DA_test3_por_ans = 0;
integer DA_test4_por_val;           parameter DA_test4_por_ans = 3;

//=======================================================================================
//  ATPG_VAL                                                                              
//=======================================================================================
integer DA_test1_atpg_val;           parameter DA_test1_atpg_ans = 1;
//integer DA_test2_atpg_val;           parameter DA_test2_atpg_ans = 0;
integer DA_test3_atpg_val;           parameter DA_test3_atpg_ans = 0;
integer DA_test4_atpg_val;           parameter DA_test4_atpg_ans = 0;

//=======================================================================================
//  SUSP_VAL                                                                              
//=======================================================================================
integer DA_test1_susp_val;           parameter DA_test1_susp_ans = 1;
integer DA_test2_susp_val;           parameter DA_test2_susp_ans = 0;
integer DA_test3_susp_val;           parameter DA_test3_susp_ans = 0;
integer DA_test4_susp_val;           parameter DA_test4_susp_ans = 0;

//=======================================================================================
//  assert_ADinterface                                                                   
//=======================================================================================
always@(*) 
begin
    if(por_chk_event)
    begin
        por_chk = 1'b1;
        $display("[ASSERT] POR check @ %t", $realtime);
        DA_test1_por_val                =  DA_test1; 
        DA_test2_por_val                =  DA_test2; 
        DA_test3_por_val                =  DA_test3; 
        DA_test4_por_val                =  DA_test4;

        ap_chk_por_DA_test1:            assert(DA_test1_por_val == DA_test1_por_ans)
                                        else   $display("[ASSERT] Error @ %t, POR check DA_test1", $realtime);

        ap_chk_por_DA_test2:            assert(DA_test2_por_val == DA_test2_por_ans)
                                        else   $display("[ASSERT] Error @ %t, POR check DA_test2", $realtime);

        ap_chk_por_DA_test3:            assert(DA_test3_por_val == DA_test3_por_ans)
                                        else   $display("[ASSERT] Error @ %t, POR check DA_test3", $realtime);

        ap_chk_por_DA_test4:            assert(DA_test4_por_val == DA_test4_por_ans)
                                        else   $display("[ASSERT] Error @ %t, POR check DA_test4", $realtime);
    end
end

always@(*)
begin
    if(atpg_chk_event)
    begin
        atpg_chk = 1'b1;
        $display("[ASSERT] ATPG check @ %t", $realtime);
        DA_test1_atpg_val               =  DA_test1; 
        //DA_test2_atpg_val               =  DA_test2; 
        DA_test3_atpg_val               =  DA_test3; 
        DA_test4_atpg_val               =  DA_test4;

        ap_chk_atpg_DA_test1:           assert(DA_test1_atpg_val == DA_test1_atpg_ans)
                                        else   $display("[ASSERT] Error @ %t, ATPG check DA_test1", $realtime);

        //ap_chk_atpg_DA_test2:           assert(DA_test2_atpg_val == DA_test2_atpg_ans)
        //                                else   $display("[ASSERT] Error @ %t, ATPG check DA_test2", $realtime);

        ap_chk_atpg_DA_test3:           assert(DA_test3_atpg_val == DA_test3_atpg_ans)
                                        else   $display("[ASSERT] Error @ %t, ATPG check DA_test3", $realtime);

        ap_chk_atpg_DA_test4:           assert(DA_test4_atpg_val == DA_test4_atpg_ans)
                                        else   $display("[ASSERT] Error @ %t, ATPG check DA_test4", $realtime);
    end
end

always@(*)
begin
    if(susp_chk_event)
    begin
        susp_chk = 1'b1;
        $display("[ASSERT] Suspend check @ %t", $realtime);
        DA_test1_susp_val               =  DA_test1; 
        DA_test2_susp_val               =  DA_test2; 
        DA_test3_susp_val               =  DA_test3; 
        DA_test4_susp_val               =  DA_test4;

        ap_chk_susp_DA_test1:           assert(DA_test1_susp_val == DA_test1_susp_ans)
                                        else   $display("[ASSERT] Error @ %t, Suspend check DA_test1", $realtime);

        ap_chk_susp_DA_test2:           assert(DA_test2_susp_val == DA_test2_susp_ans)
                                        else   $display("[ASSERT] Error @ %t, Suspend check DA_test2", $realtime);

        ap_chk_susp_DA_test3:           assert(DA_test3_susp_val == DA_test3_susp_ans)
                                        else   $display("[ASSERT] Error @ %t, Suspend check DA_test3", $realtime);

        ap_chk_susp_DA_test4:           assert(DA_test4_susp_val == DA_test4_susp_ans)
                                        else   $display("[ASSERT] Error @ %t, Suspend check DA_test4", $realtime);
    end
end


//=========================================================================================
// Assertion Summary 
//=========================================================================================
final
begin
    $display("");
    $display("[ASSERT] ADInterface Assertion Summary");
    $display("[ASSERT] NA         : no need to check");
    $display("[ASSERT] NoE        : no check event");
    $display("[ASSERT] val1       : val1 read and Pass");
    $display("[ASSERT] val1(val2) : val1 read but val2 should be read instead");
    $display("[ASSERT] =======================================================================");
    $display("[ASSERT] |Signal                           |%10s |%10s |%10s |", "POR", "ATPG", "Suspend");
    $display("[ASSERT] =======================================================================");
    $display("[ASSERT] |DA_test1                         |%10s |%10s |%10s |", chk_result_log(0, por_chk, DA_test1_por_val, DA_test1_por_ans), chk_result_log(0, atpg_chk, DA_test1_atpg_val, DA_test1_atpg_ans), chk_result_log(0, susp_chk, DA_test1_susp_val, DA_test1_susp_ans));
    $display("[ASSERT] |DA_test2                         |%10s |%10s |%10s |", chk_result_log(0, por_chk, DA_test2_por_val, DA_test2_por_ans), chk_result_log(1, atpg_chk,                 1,                 1), chk_result_log(0, susp_chk, DA_test2_susp_val, DA_test2_susp_ans));
    $display("[ASSERT] |DA_test3                         |%10s |%10s |%10s |", chk_result_log(0, por_chk, DA_test3_por_val, DA_test3_por_ans), chk_result_log(0, atpg_chk, DA_test3_atpg_val, DA_test3_atpg_ans), chk_result_log(0, susp_chk, DA_test3_susp_val, DA_test3_susp_ans));
    $display("[ASSERT] |DA_test4                         |%10s |%10s |%10s |", chk_result_log(0, por_chk, DA_test4_por_val, DA_test4_por_ans), chk_result_log(0, atpg_chk, DA_test4_atpg_val, DA_test4_atpg_ans), chk_result_log(0, susp_chk, DA_test4_susp_val, DA_test4_susp_ans));
    $display("[ASSERT] =======================================================================");
end

endmodule
