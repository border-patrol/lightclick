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

pparser = module
{
  clk  : logic    clock input  high
, rst  : logic    reset input  low

  // 32-bit LL in
, data_in    : ttBit data    input  high
, src_rdy_in : logic control input  low
, dst_rdy_in : logic control output low
, sof_in     : logic control input  low
, eof_in     : logic control input  low

  // RuleBase Out Admin

, update_out : logic info output low

// RuleBase Out Search

, five_tuple_out : ipheader data output high

  // 32 bit LL out
, data_out    : ttBit data    output high
, src_rdy_out : logic control output low
, dst_rdy_out : logic control input  low
, sof_out     : logic control output low
, eof_out     : logic control output low

};

pbuffer = module
{
  clk  : logic    clock input  high
, rst  : logic    reset input  low

  // 32 Bit LL in
, data_in    : ttBit data    input  high
, src_rdy_in : logic control input  low
, dst_rdy_in : logic control output low
, sof_in     : logic control input  low
, eof_in     : logic control input  low

// 32 Bit LL out
, data_out    : ttBit data    output high
, src_rdy_out : logic control output low
, dst_rdy_out : logic control input  low
, sof_out     : logic control output low
, eof_out     : logic control output low

};

decider = module
{
  clk  : logic    clock input  high
, rst  : logic    reset input  low

// 32 Bit LL in
, data_in    : ttBit data    input  high
, src_rdy_in : logic control input  low
, dst_rdy_in : logic control output low
, sof_in     : logic control input  low
, eof_in     : logic control input  low

  // RuleBase In ReadMem
, result_in : logic info input high

// 32 Bit LL out
, data_out    : ttBit data    output high
, src_rdy_out : logic control output low
, dst_rdy_out : logic control input  low
, sof_out     : logic control output low
, eof_out     : logic control output low

};

rulebase = module
{
  clk  : logic    clock input  high
, rst  : logic    reset input  low

  // Admin in
, update_in : logic info input low

  // Search in
, five_tuple_in : ipheader data input high

  // Result out
, result_out : logic info output high
};

oconv = module
{
  clk  : logic    clock input  high
, rst  : logic    reset input  low

// 32-Bit LL in
, data_in    : ttBit data    input  high
, src_rdy_in : logic control input  low
, dst_rdy_in : logic control output low
, sof_in     : logic control input  low
, eof_in     : logic control input  low

// 8-bit LL out
, data_out    : eightBit data    output high
, src_rdy_out : logic    control output low
, dst_rdy_out : logic    control input  low
, sof_out     : logic    control output low
, eof_out     : logic    control output low

};

connections

// Clocks & Resets
sys[clk] -> { mac[clk]
            , iconv[clk]
            , pparser[clk]
            , pbuffer[clk]
            , decider[clk]
            , rulebase[clk]
            , oconv[clk]
            };
sys[rst] -> { mac[rst]
            , iconv[rst]
            , pparser[rst]
            , pbuffer[rst]
            , decider[rst]
            , rulebase[rst]
            , oconv[rst]
            };

// MAC to iconv
mac[data_out   ]  -> iconv[data_in   ];
mac[src_rdy_out]  -> iconv[src_rdy_in];
iconv[dst_rdy_in] -> mac[dst_rdy_out];
mac[sof_out    ]  -> iconv[sof_in    ];
mac[eof_out    ]  -> iconv[eof_in    ];

// iconv to PP
iconv[data_out   ]  -> pparser[data_in   ];
iconv[src_rdy_out]  -> pparser[src_rdy_in];
pparser[dst_rdy_in] -> iconv[dst_rdy_out];
iconv[sof_out    ]  -> pparser[sof_in    ];
iconv[eof_out    ]  -> pparser[eof_in    ];

// PP to RuleBase
pparser[update_out]     -> rulebase[update_in];
pparser[five_tuple_out] -> rulebase[five_tuple_in];

// PP to PB
pparser[data_out   ] -> pbuffer[data_in   ];
pparser[src_rdy_out] -> pbuffer[src_rdy_in];
pbuffer[dst_rdy_in]  -> pparser[dst_rdy_out];
pparser[sof_out    ] -> pbuffer[sof_in    ];
pparser[eof_out    ] -> pbuffer[eof_in    ];

// PB to decider
pbuffer[data_out   ] -> decider[data_in   ];
pbuffer[src_rdy_out] -> decider[src_rdy_in];
decider[dst_rdy_in]  -> pbuffer[dst_rdy_out];
pbuffer[sof_out    ] -> decider[sof_in    ];
pbuffer[eof_out    ] -> decider[eof_in    ];

// Rulebase to Decider.

rulebase[result_out] -> decider[result_in];

// Decider to oconv
decider[data_out   ] -> oconv[data_in   ];
decider[src_rdy_out] -> oconv[src_rdy_in];
oconv[dst_rdy_in]    -> decider[dst_rdy_out];
decider[sof_out    ] -> oconv[sof_in    ];
decider[eof_out    ] -> oconv[eof_in    ];

// oconv to MAC
oconv[data_out   ] -> mac[data_in   ];
oconv[src_rdy_out] -> mac[src_rdy_in];
mac[dst_rdy_in]    -> oconv[dst_rdy_out];
oconv[sof_out    ] -> mac[sof_in    ];
oconv[eof_out    ] -> mac[eof_in    ];
