/*

An example of LocalLink orchestration.

*/

data

point = struct { x : logic, y : logic };

modules

system = module
{
  clck : logic clock output high
, rset : logic reset output high
};

producer = module
{
  clck : logic clock input high
, rset : logic reset input high

, buffer : point data output high

, ready_src : logic control output low
, ready_dst : logic control input  low

, frame_start : logic control output low
, frame_end   : logic control output low

, payload_start : logic control output low
, payload_end   : logic control output low

, error : logic control input low
};

receiver = module
{
  clck : logic clock input high
, rset : logic reset input high

, buffer : point data input high

, ready_src : logic control input  low
, ready_dst : logic control output low

, frame_start : logic control input low
, frame_end   : logic control input low

, payload_start : logic control input low
, payload_end   : logic control input low

, error : logic control output low
};

connections

system[clck] -> { producer[clck], receiver[clck] };
system[rset] -> { producer[rset], receiver[rset] };

producer[buffer] -> receiver[buffer];

producer[ready_src] -> receiver[ready_src];
receiver[ready_dst] -> producer[ready_dst];

producer[frame_start] -> receiver[frame_start];
producer[frame_end]   -> receiver[frame_end];

producer[payload_start] -> receiver[payload_start];
producer[payload_end]   -> receiver[payload_end];

receiver[error] -> producer[error];
