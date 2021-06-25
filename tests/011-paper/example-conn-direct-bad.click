model lightclick

modules

system = module { clk : logic clock output high };
scrub = module { clk : logic clock input high, ready : logic control input high,dirty : logic[32] data input high, clean : logic[32] data output high };
client = module { clk : logic clock input high, ready : logic control output high,data_i : logic[32] data input high, data_o : logic[32] data output high };

connections

system[clk]   -> scrub[ready];
client[ready] -> scrub[clk];


// -- [ EOF ]
