data

X  = struct { x : logic} ;

Y  = union { x : logic, y : X} ;

IJ = union { x : logic, y : X} ;

//Z  = Y[4] ;

modules

clk = module { c : logic clock output high } ;

init = module
  { c     : logic    clock   input  high
  , ctrl  : logic[2] control output high
  , chan1 : Y        data    output high
  , chan2 : Y        data    output  high
  , err   : logic    info    input  low
  };

trgt = module
  { c   : logic clock input  high
  , xy  : IJ    data  input  high
  , err : logic info  output low
  };

connections

// Fanouts
clk[c] -> {init[c], trgt[c]};

// Multiplexers
{ init[chan1], init[chan2] } -( init[ctrl] )-> trgt[xy];

// Direct connection
trgt[err] -> init[err];


/*
typedef struct{logic x} X;

typedef union{logic x;X y} Y;

typedef union{logic x;X y} IJ;

module clk (output logic c);
endmodule

module init (input logic c,output logic[2] ctrl,output Y chan1,output Y chan2,input net err);
endmodule

module trgt (input logic c,input IJ xy,output net err);
endmodule

module mux_trgt-xy_init-ctrl_init-chan1-init-chan2 (input logic[2] ctrl,output IJ xy,input Y chan1,input Y chan2);
endmodule

begin Top ();
    logic fan_out_from_clk-c_to_init-c-trgt-c;
    logic[2] mux_trgt-xy_init-ctrl_init-chan1-init-chan2_control;
    net trgt-err-init-err;
    IJ mux_trgt-xy_init-ctrl_init-chan1-init-chan2_output;
    IJ mux_trgt-xy_init-ctrl_init-chan1-init-chan2_input;
    IJ mux_trgt-xy_init-ctrl_init-chan1-init-chan2_fanin-init-chan1-chan1;
    IJ mux_trgt-xy_init-ctrl_init-chan1-init-chan2_fanin-init-chan2-chan2;
    init lightclick_module_0(.c(fan_out_from_clk-c_to_init-c-trgt-c)
                            ,.ctrl(mux_trgt-xy_init-ctrl_init-chan1-init-chan2_control)
                            ,.chan1(mux_trgt-xy_init-ctrl_init-chan1-init-chan2_fanin-init-chan1-chan1)
                            ,.chan2(mux_trgt-xy_init-ctrl_init-chan1-init-chan2_fanin-init-chan2-chan2)
                            ,.err(trgt-err-init-err));
    trgt lightclick_module_1(.c(fan_out_from_clk-c_to_init-c-trgt-c)
                            ,.xy(mux_trgt-xy_init-ctrl_init-chan1-init-chan2_input)
                            ,.err(trgt-err-init-err));
    mux_trgt-xy_init-ctrl_init-chan1-init-chan2 lightclick_module_2(.ctrl(mux_trgt-xy_init-ctrl_init-chan1-init-chan2_control)
                                                                   ,.xy(mux_trgt-xy_init-ctrl_init-chan1-init-chan2_input)
                                                                   ,.chan1(mux_trgt-xy_init-ctrl_init-chan1-init-chan2_fanin-init-chan1-chan1)
                                                                   ,.chan2(mux_trgt-xy_init-ctrl_init-chan1-init-chan2_fanin-init-chan2-chan2));
    clk lightclick_module_3(.c(fan_out_from_clk-c_to_init-c-trgt-c));

endmodule
*/
