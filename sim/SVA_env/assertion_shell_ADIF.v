//=============================
// Assertion Module Bind
//=============================
bind U1.U1.U_TG assert_checker_ADIF my_ADIF_checker(
    .*,
    .rstb(C_purstb),
    .atpg(1'b0),
    .susp(1'b0)
);
