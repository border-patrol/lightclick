model lightclick

modules

scrub = module { clk    : logic     clock   input  high
               , ready  : logic     control input  high
               , data_i : logic[32] data    input  high
               , data_o : logic[32] data    output high
               }
               ;

world = module { clk    : logic     clock   output high
               , ready  : logic     control output high
               , data_i : logic[32] data    output high
               , data_o : logic[32] data    input  high
               };

connections

scrub[data_o] -> world[data_o];
world[data_i] -> scrub[data_i];

world[clk]   -> scrub[clk];
world[ready] -> scrub[ready];
