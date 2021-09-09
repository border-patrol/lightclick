\\\ An example lightclick program.
model lightclick

modules

system
  = module
  { clk   : logic     output
  , rst   : logic     output
  , ready : logic     input
  , dirty : logic[32] output
  , clean : logic[32] input
  };

scrub
  = module
  { clk    : logic     input
  , rst    : logic     input
  , ready  : logic     output
  , data_i : logic[32] input
  , data_o : logic[32] output
  };

connections

system[clk]   -> scrub[rst];   // error is here
system[rst]   -> scrub[clk];   // we have swapped the reset and clock signals.
scrub[ready]  -> system[ready];
system[dirty] -> scrub[data_i];

scrub[data_o] -> system[clean];

// [ EOF ]
