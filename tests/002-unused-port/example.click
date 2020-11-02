model lightclick

modules

s = module {ctrl : logic control output high};
a = module {inA  : logic data    output high};
b = module {inB  : logic data    output high};
c = module {outc : logic data    input  high, outb : logic data input low};

connections

{ a[inA], b[inB] } -(s[ctrl])-> c[outc];
