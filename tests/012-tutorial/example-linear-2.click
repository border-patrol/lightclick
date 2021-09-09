\\\ An example lightclick program.
model lightclick

modules

system
  = module
  { clk   : logic     clock   output
  , rst   : logic     reset   output
  , ready : logic     control input
  , dirty : logic[64] data    output
  , clean : logic[64] data    input
  };

stepDown
  = module
  { clk    : logic     clock input
  , data_i : logic[64] data  input
  , data_o : logic[32] data  output
  };

stepUp
  = module
  { clk    : logic     clock input
  , data_o : logic[64] data  output
  , data_i : logic[32] data  input
  };

scrub
  = module
  { clk    : logic     clock   input
  , rst    : logic     reset   input
  , ready  : logic     control output
  , data_i : logic[32] data    input
  , data_o : logic[32] data    output
  };

connections

system[clk] -> {scrub[clk], stepUp[clk], stepDown[clk] };

system[rst]   -> scrub[rst];
scrub[ready]  -> system[ready];

system[dirty] -> stepDown[data_i]; stepDown[data_o] -> scrub[data_i];
scrub[data_o] -> stepUp[data_i]; stepUp[data_o] -> system[clean];

// [ EOF ]
