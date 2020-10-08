data

eightBit = logic[8];
ttBit = logic[32];

ip_address  = logic[32];
ip_port     = logic[16];
ip_protocol = logic[8];

ipheader = struct
{
  srcAdr   : ip_address   // 32
, srcPort  : ip_port      // 16
, dstAdr   : ip_address   // 32
, dstPort  : ip_port      // 16
, protocol : ip_protocol  //  8
};

modules

sys = module
{ clk : logic clock output high
, rst : logic reset output low
};

mac = module
{
  // GMII in -- not included
  clk  : logic    clock input  high
, rst  : logic    reset input  low

  // 8-Bit LL out
, data_out    : eightBit data    output high
, src_rdy_out : logic    control output low
, dst_rdy_out : logic    control input  low
, sof_out     : logic    control output low
, eof_out     : logic    control output low


  // 8-Bit LL in
, data_in    : eightBit data    input  high
, src_rdy_in : logic    control input  low
, dst_rdy_in : logic    control output low
, sof_in     : logic    control input  low
, eof_in     : logic    control input  low

// GMII out -- not included
};

iconv = module
{
  clk  : logic    clock input  high
, rst  : logic    reset input  low

  // 8-Bit LL in
, data_in    : eightBit data    input  high
, src_rdy_in : logic    control input  low
, dst_rdy_in : logic    control output low
, sof_in     : logic    control input  low
, eof_in     : logic    control input  low

  // 32-bit LL out
, data_out    : ttBit data    output high
, src_rdy_out : logic control output low
, dst_rdy_out : logic control input  low
, sof_out     : logic control output low
, eof_out     : logic control output low
};



connections

// Clocks & Resets
sys[clk] -> { mac[clk]
            , iconv[clk]
            };
sys[rst] -> { mac[rst]
            , iconv[rst]
            };

// MAC to iconv
mac[data_out   ]  -> iconv[data_in   ];
mac[src_rdy_out]  -> iconv[src_rdy_in];
iconv[dst_rdy_in] -> mac[dst_rdy_out];
mac[sof_out    ]  -> iconv[sof_in    ];
mac[eof_out    ]  -> iconv[eof_in    ];
