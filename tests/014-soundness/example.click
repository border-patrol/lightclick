model lightclick

types

ty = enum {a,b,c};

modules

a = module
  { clk : logic inout high
  , rst : logic output high optional
  };

b = module {clk : logic input  high};

connections

a[clk] -> b[clk];
