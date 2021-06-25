model lightclick

modules

system
  = module
    { clk : logic clock output high
    };

scrub
  = module
    { clk   : logic     clock   input  high
    , ready : logic     control input  high
    , dirty : logic[32] data    input  high
    , clean : logic[32] data    output high
    };

client
  = module
    { clk    : logic     clock   input  high
    , ready  : logic     control output high
    , data_i : logic[32] data    input  high
    , data_o : logic[32] data    output high
    };

client_d
  = module
    { clk    : logic     clock   input  high
    , ready  : logic     control output high
    , data_i : logic[32] data    input  high
    , data_o : logic[32] data    output high
    };

decider
  = module
    { inA : logic    control input  high
    , inB : logic    control input  high
    , out : logic[2] control output high };

clone
  = module
    { in   : logic[2] control input  high
    , outA : logic[2] control output high
    , outB : logic[2] control output high
    };

reduce
  = module
    { in  : logic[2] control input  high
    , out : logic    control output high
    };

connections

system[clk] -> { scrub[clk], client[clk], client_d[clk] };

client[ready]   -> decider[inA];
client_d[ready] -> decider[inB];

decider[out] -> clone[in];

{ client[data_o], client_d[data_o] } -(clone[outA])-> scrub[dirty];


clone[outB] -> reduce[in];
reduce[out] -> scrub[ready];

scrub[clean] -> { client[data_i], client_d[data_i] };


// -- [ EOF ]
