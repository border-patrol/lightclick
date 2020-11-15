model lightclick

modules

system = module { clk : logic clock output high };

scrub = module
{
   clk   : logic     clock   input  high
 , ready : logic     control input  high
 , dirty : logic[32] data    input  high
 , clean : logic[32] data    output high
};

client = module
{
   clk    : logic     clock   input  high
 , ready  : logic     control output high
 , data_i : logic[32] data    input  high
 , data_o : logic[32] data    output high
};

client_d = module
{
   clk    : logic     clock   input  high
 , ready  : logic     control output high
 , data_i : logic[32] data    input  high
 , data_o : logic[32] data    output high
};

connections

system[clk] -> { scrub[clk], client[clk], client_d[clk] };

{ client[ready], client_d[ready] } + scrub[ready];

{ client[data_o], client_d[data_o] } + scrub[dirty];

scrub[clean] -> { client[data_i], client_d[data_i] };

// -- [ EOF ]
