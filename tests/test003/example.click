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

clk[c] -> init[c]; // linearity error
