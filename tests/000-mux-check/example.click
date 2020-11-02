model lightclick

types

x = struct { x : logic} ;

y = union { x : logic, y : x} ;

z = union { x : logic, y : x} ;

modules

foo = module { x    : logic  general output high
             , ctrl : logic  control output high
             , xy   : logic  general input  high
             }
             ;

bar = module { x    : logic general input  high
             , ctrl : logic control input  high
             , xy   : logic general output high
             }
             ;

baz = module { x    : logic general input high
             , ctrl : logic control input high
             , xy   : logic general inout high
             }
             ;

baralt = module { x : logic general input high
                , y : logic general input high
                , a : logic general inout high
                }
                ;

ctrl = module { ctrl : logic control output high};

a = module { s : logic general output high };
b = module { s : logic general output high };
c = module { s : logic general output high };
d = module { s : logic general output high };

tom = module { s : logic general input high };

connections

{ a[s], b[s] } -(baz[ctrl])-> tom[s];

/*

foo[0] -> {bar[0], baz[0]};

foo[0] -> {bar[0], bar[0]};

*/

// a[s] -> bar[x];

/*
foo[0] -> baz[0];
bar[0] -> foo[0];
foo[1] -> { bar[1], baz[1] };
foo[1] -> { bar[2], baz[2] };
*/
