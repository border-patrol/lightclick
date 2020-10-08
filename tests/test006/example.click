data

x = struct { x : logic} ;
y = union { x : logic, y : x} ;
z = x[12];

modules

sys = module
{
  clk     : logic clock   output high
, selectA : logic control output high
, selectB : logic control output high
};

alice = module
{
  clk    : logic clock   input  high
, active : logic control output high
, buf    : x   data    inout  high
};

bob = module
{
  clk    : logic clock   input  high
, active : logic control output high
, buf    : x   data    inout  high
};

charlie = module
{
  clk    : logic clock   input high
, active : logic control input low
};

dave = module
{
  clk    : logic clock   input high
, active : logic control input high
, buf    : x   data    input high
};

connections

sys[clk] -> {alice[clk], bob[clk], charlie[clk], dave[clk]};

{ alice[active], bob[active] } -(sys[selectA])-> dave[active];

{ alice[buf], bob[buf] } -(sys[selectB])-> dave[buf];
