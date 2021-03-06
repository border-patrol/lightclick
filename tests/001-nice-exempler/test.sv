typedef struct packed
{
  logic x ;
} X;

typedef union packed
{
  logic x ;
  X y ;
} Y;

typedef union packed
{
  logic x ;
  X y ;
} IJ;

module clk
(
  output logic c
);
// TO ADD
endmodule;

module init
(
  input logic c,
  output logic[1:0] ctrl,
  output Y chan1,
  output Y chan2,
  input logic err
);
// TO ADD
endmodule;

module trgt
(
  input logic c,
  input IJ xy,
  output logic err
);
// TO ADD
endmodule;

module mux_trgt_xy_init_ctrl_init_chan1_init_chan2
(
  input logic[1:0] ctrl,
  output IJ xy,
  input Y chan1,
  input Y chan2
);
// TO ADD
endmodule;

module Top ();
  logic fan_out_from_clk_c_to_init_c_trgt_c;
  logic[1:0] mux_trgt_xy_init_ctrl_init_chan1_init_chan2_control;
  logic trgt_err_init_err;
  IJ mux_trgt_xy_init_ctrl_init_chan1_init_chan2_output;
  IJ mux_trgt_xy_init_ctrl_init_chan1_init_chan2_fanin_init_chan1_chan1;
  IJ mux_trgt_xy_init_ctrl_init_chan1_init_chan2_fanin_init_chan2_chan2;
  init lightclick_module_0
     (
       .c(fan_out_from_clk_c_to_init_c_trgt_c),
       .ctrl(mux_trgt_xy_init_ctrl_init_chan1_init_chan2_control),
       .chan1(mux_trgt_xy_init_ctrl_init_chan1_init_chan2_fanin_init_chan1_chan1),
       .chan2(mux_trgt_xy_init_ctrl_init_chan1_init_chan2_fanin_init_chan2_chan2),
       .err(trgt_err_init_err)
     );
  trgt lightclick_module_1
     (
       .c(fan_out_from_clk_c_to_init_c_trgt_c),
       .xy(mux_trgt_xy_init_ctrl_init_chan1_init_chan2_output),
       .err(trgt_err_init_err)
     );
  mux_trgt_xy_init_ctrl_init_chan1_init_chan2 lightclick_module_2
     (
       .ctrl(mux_trgt_xy_init_ctrl_init_chan1_init_chan2_control),
       .xy(mux_trgt_xy_init_ctrl_init_chan1_init_chan2_output),
       .chan1(mux_trgt_xy_init_ctrl_init_chan1_init_chan2_fanin_init_chan1_chan1),
       .chan2(mux_trgt_xy_init_ctrl_init_chan1_init_chan2_fanin_init_chan2_chan2)
     );
  clk lightclick_module_3
     (
       .c(fan_out_from_clk_c_to_init_c_trgt_c)
     );

endmodule;
