model lightclick

modules

world = module { clk     : logic     clock   output high
               , ready   : logic     control output high
               , select  : logic[2]  control output high
               , data_ia : logic[32] data    output high
               , data_ib : logic[32] data    output high
               , data_o  : logic[32] data    input  high
               };

scrub = module { clk    : logic     clock   input  high
               , ready  : logic     control input  high
               , data_i : logic[32] data    input  high
               , data_o : logic[32] data    output high
               }
               ;

connections


world[clk]   -> scrub[clk];
world[ready] -> scrub[ready];

{ world[data_ia], world[data_ib] } -( world[select] )-> scrub[data_i];

scrub[data_o] -> world[data_o];
