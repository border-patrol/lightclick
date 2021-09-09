\\\ An example lightclick program.
model lightclick

modules

system
  = module
  { clk   : logic     clock   output
  , rst   : logic     reset   output
  , ready : logic     control input
  , dirty : logic[32] data    output
  , clean : logic[32] data    input
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

system[clk]   -> scrub[rst];   // error is here
system[rst]   -> scrub[clk];   // we have swapped the reset and clock signals.
scrub[ready]  -> system[ready];
system[dirty] -> scrub[data_i];

scrub[data_o] -> system[clean];

// [ EOF ]
