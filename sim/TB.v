`timescale 1ns/1ps
`include "ModeDef.v"

`ifdef ASSERT_AD
    `include "SVA_env/assert_checker_ADinterface.v"
`endif

`ifdef ASSERT_POWER
    `include "SVA_env/assert_checker_PMU.v"
`endif

`ifdef ASSERT_GLITCH
    `include "SVA_env/assert_checker_Glitch.v"
`endif

`ifdef ASSERT_TG
    `include "SVA_env/assert_checker_TG.v"
`endif

module TB();

initial begin
`ifdef ASSERT_AD
    $display("    [ASSERT] ASSERT_AD is enabled");
`else
    $display("    [ASSERT] ASSERT_AD is disabled");
`endif

`ifdef ASSERT_POWER
    $display("    [ASSERT] ASSERT_POWER is enabled");
`else
    $display("    [ASSERT] ASSERT_POWER is disabled");
`endif

`ifdef ASSERT_GLITCH
    $display("    [ASSERT] ASSERT_GLITCH is enabled");
`else
    $display("    [ASSERT] ASSERT_GLITCH is disabled");
`endif

`ifdef ASSERT_TG
    $display("    [ASSERT] ASSERT_TG is enabled");
`else
    $display("    [ASSERT] ASSERT_TG is disabled");
`endif
end

initial begin
    #(200000);
    $finish;
end

DUT U1(
/*AUTOINST*/
       // Inouts
       .SDA				(SDA),
       .SCL				(SCL));

`ifdef ASSERT_AD
    `include "SVA_env/assertion_shell_ADinterface.v"
`endif

`ifdef ASSERT_POWER
    `include "SVA_env/assertion_shell_PMU.v"
`endif

`ifdef ASSERT_GLITCH
    `include "SVA_env/assertion_shell_Glitch.v"
`endif

`ifdef ASSERT_TG
    `include "SVA_env/assertion_shell_TG.v"
`endif

`ifdef VCDDUMP
initial begin
    $dumpfile("Test.vcd");  //
    $dumpvars(0,TB);       
end
`endif

endmodule

