model lightclick

types

ty = enum {a,b,c};

modules

a = module
  { clk : logic output high
  , rst : logic output high optional
  };

b = module {clk : logic input  high};

connections

a[clk] -> b[clk];
