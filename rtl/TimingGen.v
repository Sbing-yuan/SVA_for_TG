module TimingGen(
/*AUTOARG*/
   // Outputs
   DA_test1, DA_test2, DA_test3, DA_test4,
   // Inputs
   clk, B_test1, B_test2, B_test3, C_purstb
   );

output          DA_test1;
output          DA_test2;
output          DA_test3;
output [3:0]    DA_test4;

input           clk;         
input [3:0]     B_test1;     
input [3:0]     B_test2;     
input [3:0]     B_test3;     
input           C_purstb;     

reg          DA_test1;
reg          DA_test2;
reg          DA_test3;
reg [3:0]    DA_test4;

// Design Spec:
// B_test1 -> control DA_test1 pulse width
// B_test2 -> control DA_test2 pulse start, DA_test2_pulse fix 1T
// B_test3 -> control DA_test3 pulse start, DA_test3_pulse fix 1T
//             _______
//DA_test1 ___/       \___
//             __
//DA_test2 ___/  \________
//                 __
//DA_test3 _______/  \____
//         ___________ ________________________
//DA_test4 _____0_____|___1->3->2(grey code)___

reg [9:0] tg_cnt;

always@(posedge clk or negedge C_purstb)
    if(~C_purstb)
        tg_cnt <= 10'd0;
    else if(tg_cnt < 10'd1000)
        tg_cnt <= tg_cnt + 10'd1;
    else if(tg_cnt == 10'd1000)
        tg_cnt <= 10'd0;

wire [9:0] DA_test1_r = 10'd1;
wire [9:0] DA_test1_f = 10'd1 + {6'd0,B_test1[3:0]};
always@(posedge clk or negedge C_purstb)
    if(~C_purstb)
        DA_test1 <= 1'b0;
    else if(tg_cnt == DA_test1_f)
        DA_test1 <= 1'b0;
    else if(tg_cnt == DA_test1_r)
        DA_test1 <= 1'b1;

wire [9:0] DA_test2_r = 10'd1 + {6'd0,B_test2[3:0]};
wire [9:0] DA_test2_f = 10'd1 + DA_test2_r;
always@(posedge clk or negedge C_purstb)
    if(~C_purstb)
        DA_test2 <= 1'b0;
    else if(tg_cnt == DA_test2_f)
        DA_test2 <= 1'b0;
    else if(tg_cnt == DA_test2_r)
        DA_test2 <= 1'b1;

wire [9:0] DA_test3_r = 10'd1 + {6'd0,B_test3[3:0]};
wire [9:0] DA_test3_f = 10'd1 + DA_test3_r;
always@(posedge clk or negedge C_purstb)
    if(~C_purstb)
        DA_test3 <= 1'b0;
    else if(tg_cnt == DA_test3_f)
        DA_test3 <= 1'b0;
    else if(tg_cnt == DA_test3_r)
        DA_test3 <= 1'b1;

always@(posedge clk or negedge C_purstb)
    if(~C_purstb)
        DA_test4 <= 4'b0000;
    else if(tg_cnt == 10'd1000)
    begin
        case(DA_test4[3:0])
        4'b0000: DA_test4 <= 4'b0001;
        4'b0001: DA_test4 <= 4'b0011;
        4'b0011: DA_test4 <= 4'b0010;
        4'b0010: DA_test4 <= 4'b0110;
        4'b0110: DA_test4 <= 4'b0111;
        4'b0111: DA_test4 <= 4'b0101;
        4'b0101: DA_test4 <= 4'b0100;
        4'b0100: DA_test4 <= 4'b1100;
        4'b1100: DA_test4 <= 4'b1101;
        4'b1101: DA_test4 <= 4'b1111;
        4'b1111: DA_test4 <= 4'b1110;
        4'b1110: DA_test4 <= 4'b1010;
        4'b1010: DA_test4 <= 4'b1011;
        4'b1011: DA_test4 <= 4'b1001;
        4'b1001: DA_test4 <= 4'b1000;
        4'b1000: DA_test4 <= 4'b0000;
        default: DA_test4 <= 4'b0000;
        endcase
    end

endmodule
