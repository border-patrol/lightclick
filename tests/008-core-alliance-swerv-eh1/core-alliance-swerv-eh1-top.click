\\ In this file we present *a* high-level model of the CHIPS Alliance SweRV Core EH1 using the AHB interfaces.
\\
\\ SweRV Core EH1 is a 32-bit, 2-way superscalar, 9 stage pipeline core.
\\ More details can be found:
\\
\\ + https://github.com/chipsalliance/Cores-SweRV/
\\ + https://blog.westerndigital.com/risc-v-swerv-core-open-source/
\\ + https://chipsalliance.org/
\\
\\ In this model, we concentrate on modelling the high-level modules and their connections, as found in `swerv-wrapper.sv`, the project's top-level module that interacts with the world.
\\
\\ Where appropriate we have used the SystemVerilog names and documentation for modules andports.
\\ For ease of modelling we are using LightClick with the `verilog` compatible flag that allows port declarations to be lifted and more easily annotated directly from SystemVerilog Code.
\\
\\ This model will *fail* to type-check successfully, and will produce the error message:
\\
\\ ```sh
\\ LOG: Parsing Complete
\\ LOG: MetaTyping Complete
\\ Error Happened
\\ Unused ports:
\\          - dmi_wrapper ["tdoEnable"]
\\          - world ["mbist_mode"]
\\ LOG: Typing Complete
\\ ```
\\
\\ The ports:
\\
\\ + `tdoEnable()` of `dmi_wrapper`, an output port
\\ + `mbist_mode`  of `world`, an input port
\\
\\ are left dangling.
\\
\\ These are two control signals that are not apprently used in the design at the level of modelling here.
\\ This is a prime example of things LightClick *cannot* encode: dangling ports.
\\ We require that *all* ports must be used.
\\ Now one can imagine that it seems reasonable for dangling ports to be okay.
\\ Otherwise the SweRV engineers would not specify these ports.
\\ However, the safety of dangling ports is dependent on their intended usage, and we are working in a system of usages.
\\ Usages be it physical wiring or intended use is a cross interface substructural property dependent on the protocol (standardised or otherwise) being realised.
\\ This means that if this property is not known then the physical port linearity must be Sith like: absolute!
\\ The rationale here is that we don't have enough information in the type-system to *know* which signals are 'optional' and which are not.
\\ It is perfectly reasonable to optional output signals to be left dangling but not required signals.
\\ How we resolve this is left for future work that will involve embedding some existing sub-structural typing of hardware interfaces into LightClick [conf/ecoop/Muijnck-HughesV19].
\\
\\ Of interest in this particular case is that `tdoEnable` has a known source and usage through out the design, and `mbist_mode` does not. The port `tdoEnable` of `dmi_wrapper` is an output port and has a defined source within the remainder of the design. The port `mbist_mode` is an input port from the world and from analysis of the source code is not used within the design.

model lightclick verilog

// # Data types
//
// We begin our modeling of SweRV EH1 by first describing the data types to be used.
//
// SystemVerilog supports a complex set of data types that have very interesting substructural properties that we are also exploring.
// In this paper we are, however, concentrating on typing Modules and their interconnections rather than the data types themselves.
//
// Thus for each data type used by SweRV EH1 we will replicate their representation as faithfully as possible in LightClick.
// This will not always result into a 1-2-1 mapping, however, this should not detract from our modelling of Ibex.
// For instance, SystemVerilog uses value based enumerations (mappings of labels to values) to represent various  enumerations, we have replaced them with simple bit-vectors.

types

// ## Aliases.
//
// Here we present several type-synonms to making writing the interfaces easier.

\\ Represents `logic [31:1]`
logic30 = logic[30];

logic64 = logic[64];

logic2 = logic[2];

logic3 = logic[3];

logic4 = logic[4];

logic5 = logic[5];

logic32 = logic[32];

logic8 = logic[8];

// ## parameters
//
// The SweRV code is parameterised with user chosen SV macros.
// LightClick does not allow macro definitions nor parameterisation of interfaces.
// We pin this values explicitly as type-synonms based on an existing configuration sourced online:
//
//  https://github.com/yzt000000/swerv_sim/blob/2e2638bf72e5ac41e80ccef79a3d83c298ef7701/src/configs/snapshots/default/defines.h

rv_pic_total_int    = logic[7];  // This is a parameter.
rv_dccm_bits        = logic[14]; // [`RV_DCCM_BITS-1:0]
rv_dccm_data_width  = logic[32];
rv_dccm_fdata_width = logic[38]; // [`RV_DCCM_FDATA_WIDTH-1:0]
rv_iccm_bits        = logic[16]; // [`RV_ICCM_BITS-1:2]

// # Modules
modules

// Here we describe the various *required* modules within the design.
// SweRV EH1 collects various stages of the pipeline into discreate modules.
// LightClick doesn't support module hierarchies, nor parameterised modules, and we have flattened the module structure as appropriate.
//
// Further, SweRV EH1 supports either the AXI-Lite protocol, or AHB.
// Within the code for SweRV EH1 the AXI interfaces have several signals (i.e. AWID & RWID) whose length is determined by a SystemVerilog macro.
// Neither the project and AXI documentation ascertains precisely what size these, and other macro'd signals can be.
// Thus, we have chosen to model the SoC using AHB whose signal sizes is staticly known.
//
// Chosen to enable `RV_ICACHE_ECC`.
//
// LightClick supports type-level annotations over ports.
// Two of these annotations are not found in SystemVerilog: Port usage and sensitivity.
// For each, port we make best guess effort to determine their values, refering to the standards where applicable.
//
// ## Modelling AHB0Lite.
//
// Here we present a break down of the AHB signal list. We copy documentation from the Standard.
//
// | Source    | Sensitivity | Intent  | Type         | Name          | Description                                                                                                                           |
// |-----------+-------------+---------+--------------+---------------+---------------------------------------------------------------------------------------------------------------------------------------|
// | in-Always | Rising      | Clock   | logic        | HCLK          | All signal timings are related to the rising edge of HCLK                                                                             |
// | in-Always | Low         | Reset   | logic        | HRESETn       | The bus reset signal is active LOW and is used to reset the system and the bus. This is the only active LOW signal.                   |
// | Driver    | High        | Address | logic [31:0] | HADDR         | The 32-Bit system address bus.                                                                                                        |
// | Driver    | High        | Info    | logic [2:0]  | HBURST        | The burst type indicates if the transfer is a single transfer or forms part of a burst.                                                                                                                                      |
// | Driver    | High        | Info    | logic        | HMASTLOCK     | Indicates that the current master is performing a locked sequence of transfers. This signal has the same timing as the HMASTER signal |
// | Driver    | High        | Info    | logic [1:0]  | HTRANS        | Indicates the type of the curent transfer                                                                                             |
// | Driver    | Insensitive | Control | logic        | HWRITE        | When HIGH this signal indicates a write transfer and when LOW a read transfer.                                                        |
// | Driver    | High        | Info    | logic[2:0]   | HSIZE         | Indicates the size of the transfer, which is typically byte (8-bit), halfword (16-bit) or word (32-bit).                              |
// | Driver    | High        | Control | logic[3:0]   | HPROT         | The protection control signals provide additional information about a bus access.                                                     |
// | Driver    | High        | Data    | logic[31:0]  | HWDATA        | The write data bus is used to transfer data from the master to the bus slaves during write operations.                                |
// | Receiver  | High        | Data    | logic[31:0]  | HRDATA        | The read data bus is used to transfer data from bus slaves to the bus master during read operations.                                  |
// | Receiver  | Insensitive | Control | logic        | HREADY_DR     | When HIGH this signal indicates that a transfer has finished on the bus, it may be driven LOW to extend a transfer.                   |
// | Receiver  | High        | Control | logic        | HREADY_RD_OUT | Note: Slaves on the bus require HREADY as both an input and an output signal.                                                         |
// | Receiver  | High        | Control | logic        | HREADY_RD_IN  |                                                                                                                                       |
// | Receiver  | High        | Info    | logic        | HRESP         | The transfer response provides additional information on the status of a transfer.                                                    |

// ## The World

\\ LightClick expects 'closed' designs.
\\
\\ For this example, the 'world' represents the deployment specific signals required by SweRV EH1.
\\ This corresponds to the `swerv_warapper.sv` top module with the directionality of it's ports mirrored to act as a providing interface.
\\
world = module
{
   output high clock   logic   clk,
   output low  reset   logic   rst_l,
   output low  reset   logic   dbg_rst_l,
   output high reset   logic30 rst_vec,
   output high general logic   nmi_int,
   output high general logic30 nmi_vec,
   output high info    logic30 jtag_id,


   input high info      logic64 trace_rv_i_insn_ip,
   input high info      logic64 trace_rv_i_address_ip,
   input high info      logic3  trace_rv_i_valid_ip,
   input high info      logic3  trace_rv_i_exception_ip,
   input high info      logic5  trace_rv_i_ecause_ip,
   input high interrupt logic3  trace_rv_i_interrupt_ip,
   input high info      logic32 trace_rv_i_tval_ip,


   // Bus signals

   //// AHB LITE BUS
   input  high        address logic32 haddr,
   input  high        info    logic3  hburst,
   input  high        info    logic   hmastlock,
   input  high        control logic4  hprot,
   input  high        info    logic3  hsize,
   input  high        info    logic2  htrans,
   input  insensitive control logic   hwrite,

   output high        data    logic64 hrdata,
   output insensitive control logic   hready,
   output high        info    logic   hresp,

   // LSU AHB Master
   input  high        address logic32 lsu_haddr,
   input  high        info    logic3  lsu_hburst,
   input  high        info    logic   lsu_hmastlock,
   input  high        control logic4  lsu_hprot,
   input  high        info    logic3  lsu_hsize,
   input  high        info    logic2  lsu_htrans,
   input  insensitive control logic   lsu_hwrite,
   input  high        data    logic64 lsu_hwdata,

   output high        data    logic64 lsu_hrdata,
   output insensitive control logic   lsu_hready,
   output high        info    logic   lsu_hresp,

   // Debug Syster Bus AHB
   input high         address logic32 sb_haddr,
   input high         info    logic3  sb_hburst,
   input high         info    logic   sb_hmastlock,
   input high         control logic4  sb_hprot,
   input high         info    logic3  sb_hsize,
   input high         info    logic2  sb_htrans,
   input insensitive  control logic   sb_hwrite,
   input high         data    logic64 sb_hwdata,

   output high        data    logic64 sb_hrdata,
   output insensitive control logic   sb_hready,
   output high        info    logic   sb_hresp,

   // DMA Slave
   output high        address logic32 dma_haddr,
   output high        info    logic3  dma_hburst,
   output high        info    logic   dma_hmastlock,
   output high        control logic4  dma_hprot,
   output high        info    logic3  dma_hsize,
   output high        info    logic2  dma_htrans,
   output insensitive control logic   dma_hwrite,
   output high        data    logic64 dma_hwdata,
   output high        control logic   dma_hsel,
   output high        control logic   dma_hreadyin,

   input  high        data    logic64 dma_hrdata,
   input  insensitive control logic   dma_hreadyout,
   input  high        info    logic   dma_hresp,

   // clk ratio signals
   output high control logic lsu_bus_clk_en, // Clock ratio b/w cpu core clk & AHB master interface
   output high control logic ifu_bus_clk_en, // Clock ratio b/w cpu core clk & AHB master interface
   output high control logic dbg_bus_clk_en, // Clock ratio b/w cpu core clk & AHB master interface
   output high control logic dma_bus_clk_en,  // Clock ratio b/w cpu core clk & AHB slave interface

   output high control logic            timer_int,
   output high control rv_pic_total_int extintsrc_req,

   input high info logic2 dec_tlu_perfcnt0, // toggles when perf counter 0 has an event inc
   input high info logic2 dec_tlu_perfcnt1,
   input high info logic2 dec_tlu_perfcnt2,
   input high info logic2 dec_tlu_perfcnt3,

   // ports added by the soc team
   output high clock   logic jtag_tck,    // JTAG clk
   output high general logic jtag_tms,    // JTAG TMS
   output high general logic jtag_tdi,    // JTAG tdi
   output low  reset   logic jtag_trst_n, // JTAG Reset
   input  high general logic jtag_tdo,    // JTAG TDO

   // external MPC halt/run interface
   output high control logic mpc_debug_halt_req, // Async halt request
   output high control logic mpc_debug_run_req, // Async run request
   output high control logic mpc_reset_run_req, // Run/halt after reset
   input  high control logic mpc_debug_halt_ack, // Halt ack
   input  high control logic mpc_debug_run_ack, // Run ack
   input  high info    logic debug_brkpt_status, // debug breakpoint


   output high control logic i_cpu_halt_req,       // Async halt req to CPU
   input  high info    logic o_cpu_halt_ack,       // core response to halt
   input  high info    logic o_cpu_halt_status,    // 1'b1 indicates core is halted
   input  high info    logic o_debug_mode_status,  // Core to the PMU that core is in debug mode. When core is in debug mode, the PMU should refrain from sendng a halt or run request
   output high control logic i_cpu_run_req,        // Async restart req to CPU
   input  high info    logic o_cpu_run_ack,        // Core response to run req
   output high control logic scan_mode,            // To enable scan mode
   output high control logic mbist_mode            // to enable mbist
};

// ## SweRV
swerv = module
{
   input  high clock   logic   clk,
   input  low  reset   logic   rst_l,
   input  low  reset   logic   dbg_rst_l,
   input  high reset   logic30 rst_vec,
   input  high general logic   nmi_int,
   input  high general logic30 nmi_vec,
   output low  reset   logic   core_rst_l,   // This is "rst_l | dbg_rst_l"

   output high info      logic64 trace_rv_i_insn_ip,
   output high info      logic64 trace_rv_i_address_ip,
   output high info      logic3  trace_rv_i_valid_ip,
   output high info      logic3  trace_rv_i_exception_ip,
   output high info      logic5  trace_rv_i_ecause_ip,
   output high interrupt logic3  trace_rv_i_interrupt_ip,
   output high info      logic32 trace_rv_i_tval_ip,

   output high control logic lsu_freeze_dc3,
   output high control logic dccm_clk_override,
   output high control logic icm_clk_override,
   output high control logic dec_tlu_core_ecc_disable,

   // external halt/run interface
   input  high control logic  i_cpu_halt_req,  // Asynchronous Halt request to CPU
   input  high control logic  i_cpu_run_req,   // Asynchronous Restart request to CPU
   output high info logic o_cpu_halt_ack,      // Core Acknowledge to Halt request
   output high info logic o_cpu_halt_status,   // 1'b1 indicates processor is halted
   output high info logic o_cpu_run_ack,       // Core Acknowledge to run request
   output high info logic o_debug_mode_status, // Core to the PMU that core is in debug mode. When core is in debug mode, the PMU should refrain from sendn a halt or run request

   // external MPC halt/run interface
   input  high control logic mpc_debug_halt_req, // Async halt request
   input  high control logic mpc_debug_run_req, // Async run request
   input  high control logic mpc_reset_run_req, // Run/halt after reset
   output high control logic mpc_debug_halt_ack, // Halt ack
   output high control logic mpc_debug_run_ack, // Run ack
   output high info    logic debug_brkpt_status, // debug breakpoint

   output high info logic2 dec_tlu_perfcnt0, // toggles when perf counter 0 has an event inc
   output high info logic2 dec_tlu_perfcnt1,
   output high info logic2 dec_tlu_perfcnt2,
   output high info logic2 dec_tlu_perfcnt3,

   // DCCM ports
   output high control logic               dccm_wren,
   output high control logic               dccm_rden,
   output high address rv_dccm_bits        dccm_wr_addr,
   output high address rv_dccm_bits        dccm_rd_addr_lo,
   output high address rv_dccm_bits        dccm_rd_addr_hi,
   output high data    rv_dccm_fdata_width dccm_wr_data,

   input  high data    rv_dccm_fdata_width dccm_rd_data_lo,
   input  high data    rv_dccm_fdata_width dccm_rd_data_hi,

   // ICCM ports
   output high address rv_iccm_bits iccm_rw_addr,
   output high control logic        iccm_wren,
   output high control logic        iccm_rden,
   output high info    logic3       iccm_wr_size,
   output high data    logic[78]    iccm_wr_data,

   input  high data    logic[156]   iccm_rd_data,

   // ICache , ITAG  ports
   output high address logic[29]  ic_rw_addr,   // logic [31:2]
   output high control logic4     ic_tag_valid,
   output high control logic4     ic_wr_en,
   output high control logic      ic_rd_en,

   output high data logic[84]   ic_wr_data,         // Data to fill to the Icache. With ECC
   input  high data logic[168]  ic_rd_data ,        // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
   input  high data logic[25] ictag_debug_rd_data,// Debug icache tag.
   output high data logic[42] ic_debug_wr_data,   // Debug wr cache.

   output high data    logic[128] ic_premux_data,     // Premux data to be muxed with each way of the Icache.
   output high control logic      ic_sel_premux_data, // Select premux data


   output high address logic[13] ic_debug_addr,      // Read/Write addresss to the Icache. // logic [15:2]
   output high control logic     ic_debug_rd_en,     // Icache debug rd
   output high control logic     ic_debug_wr_en,     // Icache debug wr
   output high general logic     ic_debug_tag_array, // Debug tag array
   output high general logic4    ic_debug_way,       // Debug way. Rd or Wr.

   input high info logic4 ic_rd_hit,
   input high info logic  ic_tag_perr,      // Icache Tag parity error

   // AHB LITE BUS
   output high        address logic32 haddr,
   output high        info    logic3  hburst,
   output high        info    logic   hmastlock,
   output high        control logic4  hprot,
   output high        info    logic3  hsize,
   output high        info    logic2  htrans,
   output insensitive control logic   hwrite,

   input high        data    logic64 hrdata,
   input insensitive control logic   hready,
   input high        info    logic   hresp,

   // LSU AHB Master
   output high        address logic32 lsu_haddr,
   output high        info    logic3  lsu_hburst,
   output high        info    logic   lsu_hmastlock,
   output high        control logic4  lsu_hprot,
   output high        info    logic3  lsu_hsize,
   output high        info    logic2  lsu_htrans,
   output insensitive control logic   lsu_hwrite,
   output high        data    logic64 lsu_hwdata,

   input high        data     logic64 lsu_hrdata,
   input insensitive control  logic   lsu_hready,
   input high        info     logic   lsu_hresp,

   //System Bus Debug Master
   output high         address logic32 sb_haddr,
   output high         info    logic3  sb_hburst,
   output high         info    logic   sb_hmastlock,
   output high         control logic4  sb_hprot,
   output high         info    logic3  sb_hsize,
   output high         info    logic2  sb_htrans,
   output insensitive  control logic   sb_hwrite,
   output high         data    logic64 sb_hwdata,

   input high        data     logic64 sb_hrdata,
   input insensitive control  logic   sb_hready,
   input high        info     logic   sb_hresp,

   // DMA Slave
   input high        address logic32 dma_haddr,
   input high        info    logic3  dma_hburst,
   input high        info    logic   dma_hmastlock,
   input high        control logic4  dma_hprot,
   input high        info    logic3  dma_hsize,
   input high        info    logic2  dma_htrans,
   input insensitive control logic   dma_hwrite,
   input high        data    logic64 dma_hwdata,
   input high        control logic   dma_hsel,
   input high        control logic   dma_hreadyin,

   output high        data    logic64 dma_hrdata,
   output insensitive control logic   dma_hreadyout,
   output high        info    logic   dma_hresp,

   input high control logic lsu_bus_clk_en,
   input high control logic ifu_bus_clk_en,
   input high control logic dbg_bus_clk_en,
   input high control logic dma_bus_clk_en,

   //Debug module
   input  high control logic    dmi_reg_en,
   input  high address logic[7] dmi_reg_addr,
   input  high control logic    dmi_reg_wr_en,
   input  high data    logic32  dmi_reg_wdata,
   output high data    logic32  dmi_reg_rdata,
   input  high reset   logic    dmi_hard_reset,

   input high general rv_pic_total_int extintsrc_req,
   input high general logic            timer_int,
   input high general logic            scan_mode
};

mem = module
{
   input high clock   logic clk,
   input low  reset   logic rst_l,
   input high control logic lsu_freeze_dc3,
   input high control logic dccm_clk_override,
   input high control logic icm_clk_override,

   input high control logic dec_tlu_core_ecc_disable,

   //DCCM ports
   input high control logic dccm_wren,
   input high control logic dccm_rden,

   input high address rv_dccm_bits        dccm_wr_addr,
   input high address rv_dccm_bits        dccm_rd_addr_lo,
   input high address rv_dccm_bits        dccm_rd_addr_hi,
   input high data    rv_dccm_fdata_width dccm_wr_data,

   output  high data    rv_dccm_fdata_width dccm_rd_data_lo,
   output  high data    rv_dccm_fdata_width dccm_rd_data_hi,

   //ICCM ports
   input  high address rv_iccm_bits iccm_rw_addr,
   input  high control logic        iccm_wren,
   input  high control logic        iccm_rden,
   input  high info    logic3       iccm_wr_size,
   input  high data    logic[78]    iccm_wr_data,

   output high data    logic[156]   iccm_rd_data,

   // Icache and Itag Ports

   input high address logic[29]  ic_rw_addr,   // logic [31:2]
   input high control logic4     ic_tag_valid,
   input high control logic4     ic_wr_en,
   input high control logic      ic_rd_en,

   input high data    logic[128] ic_premux_data,     // Premux data to be muxed with each way of the Icache.
   input high control logic      ic_sel_premux_data, // Premux data sel

   input high data logic[84] ic_wr_data,         // Data to fill to the Icache. With ECC
   input high data logic[42] ic_debug_wr_data,   // Debug wr cache.

   input high address logic[13] ic_debug_addr,      // Read/Write addresss to the Icache. // logic [15:2]
   input high control logic     ic_debug_rd_en,     // Icache debug rd
   input high control logic     ic_debug_wr_en,     // Icache debug wr
   input high general logic     ic_debug_tag_array, // Debug tag array
   input high general logic4    ic_debug_way,       // Debug way. Rd or Wr.


   output high data logic[168] ic_rd_data,          // Data read from Icache. 2x64bits + parity bits. F2 stage. With ECC
   output high data logic[25]  ictag_debug_rd_data, // Debug icache tag.


   output high info logic4 ic_rd_hit,
   output high info logic  ic_tag_perr, // Icache Tag parity error

   input  high control logic scan_mode
};

dmi_wrapper = module
{
  input high control logic scan_mode, // scan mode

  // JTAG signals
  input   low  reset   logic trst_n,              // JTAG reset
  input   high clock   logic tck,                 // JTAG clock
  input   high general logic tms,                 // Test mode select
  input   high general logic tdi,                 // Test Data Input
  output  high general logic tdo,                 // Test Data Output
  output  high general logic tdoEnable,           // Test Data Output enable

  // Processor Signals
  input  low  reset   logic    core_rst_n,    // Core reset
  input  high clock   logic    core_clk,      // Core clock
  input  high info    logic30  jtag_id,       // JTAG ID
  input  high data    logic32  rd_data,       // 32 bit Read data from  Processor
  output high data    logic32  reg_wr_data,   // 32 bit Write data to Processor
  output high address logic[7] reg_wr_addr,   // 7 bit reg address to Processor
  output high control logic    reg_en,        // 1 bit  Read enable to Processor
  output high control logic    reg_wr_en,     // 1 bit  Write enable to Processor
  output high reset   logic    dmi_hard_reset
};

connections


// ## Global Signals

world[clk]       -> {swerv[clk], mem[clk], dmi_wrapper[core_clk]};

world[rst_l]     -> swerv[rst_l];

world[dbg_rst_l] -> { swerv[dbg_rst_l]
                    , dmi_wrapper[core_rst_n] // Primary reset, active low
                    };

world[scan_mode] -> { swerv[scan_mode]
                    , mem[scan_mode]
                    , dmi_wrapper[scan_mode]
                    };

// ## Connecting SweRV

world[rst_vec]   -> swerv[rst_vec];
world[nmi_int]   -> swerv[nmi_int];
world[nmi_vec]   -> swerv[nmi_vec];

swerv[trace_rv_i_insn_ip]      -> world[trace_rv_i_insn_ip];
swerv[trace_rv_i_address_ip]   -> world[trace_rv_i_address_ip];
swerv[trace_rv_i_valid_ip]     -> world[trace_rv_i_valid_ip];
swerv[trace_rv_i_exception_ip] -> world[trace_rv_i_exception_ip];
swerv[trace_rv_i_ecause_ip]    -> world[trace_rv_i_ecause_ip];
swerv[trace_rv_i_interrupt_ip] -> world[trace_rv_i_interrupt_ip];
swerv[trace_rv_i_tval_ip]      -> world[trace_rv_i_tval_ip];

// ### external halt/run interface
world[i_cpu_halt_req] -> swerv[i_cpu_halt_req];
world[i_cpu_run_req]  -> swerv[i_cpu_run_req];

swerv[o_cpu_halt_ack]      -> world[o_cpu_halt_ack];
swerv[o_cpu_halt_status]   -> world[o_cpu_halt_status];
swerv[o_cpu_run_ack]       -> world[o_cpu_run_ack];
swerv[o_debug_mode_status] -> world[o_debug_mode_status];

// ### external MPC halt/run interface
world[mpc_debug_halt_req] -> swerv[mpc_debug_halt_req];
world[mpc_debug_run_req]  -> swerv[mpc_debug_run_req];
world[mpc_reset_run_req]  -> swerv[mpc_reset_run_req];
swerv[mpc_debug_halt_ack] -> world[mpc_debug_halt_ack];
swerv[mpc_debug_run_ack]  -> world[mpc_debug_run_ack];
swerv[debug_brkpt_status] -> world[debug_brkpt_status];

swerv[dec_tlu_perfcnt0] -> world[dec_tlu_perfcnt0];
swerv[dec_tlu_perfcnt1] -> world[dec_tlu_perfcnt1];
swerv[dec_tlu_perfcnt2] -> world[dec_tlu_perfcnt2];
swerv[dec_tlu_perfcnt3] -> world[dec_tlu_perfcnt3];

// ### AHB LITE BUS

swerv[haddr]     -> world[haddr];
swerv[hburst]    -> world[hburst];
swerv[hmastlock] -> world[hmastlock];
swerv[hprot]     -> world[hprot];
swerv[hsize]     -> world[hsize];
swerv[htrans]    -> world[htrans];
swerv[hwrite]    -> world[hwrite];

world[hrdata] -> swerv[hrdata];
world[hready] -> swerv[hready];
world[hresp]  -> swerv[hresp];

// ### LSU AHB Master

swerv[lsu_haddr]     -> world[lsu_haddr];
swerv[lsu_hburst]    -> world[lsu_hburst];
swerv[lsu_hmastlock] -> world[lsu_hmastlock];
swerv[lsu_hprot]     -> world[lsu_hprot];
swerv[lsu_hsize]     -> world[lsu_hsize];
swerv[lsu_htrans]    -> world[lsu_htrans];
swerv[lsu_hwrite]    -> world[lsu_hwrite];
swerv[lsu_hwdata]    -> world[lsu_hwdata];

world[lsu_hrdata] -> swerv[lsu_hrdata];
world[lsu_hready] -> swerv[lsu_hready];
world[lsu_hresp]  -> swerv[lsu_hresp];

// ### System Bus Debug Master

swerv[sb_haddr]     -> world[sb_haddr];
swerv[sb_hburst]    -> world[sb_hburst];
swerv[sb_hmastlock] -> world[sb_hmastlock];
swerv[sb_hprot]     -> world[sb_hprot];
swerv[sb_hsize]     -> world[sb_hsize];
swerv[sb_htrans]    -> world[sb_htrans];
swerv[sb_hwrite]    -> world[sb_hwrite];
swerv[sb_hwdata]    -> world[sb_hwdata];

world[sb_hrdata] -> swerv[sb_hrdata];
world[sb_hready] -> swerv[sb_hready];
world[sb_hresp]  -> swerv[sb_hresp];

// ### DMA Receiver.

world[dma_haddr]     -> swerv[dma_haddr];
world[dma_hburst]    -> swerv[dma_hburst];
world[dma_hmastlock] -> swerv[dma_hmastlock];
world[dma_hprot]     -> swerv[dma_hprot];
world[dma_hsize]     -> swerv[dma_hsize];
world[dma_htrans]    -> swerv[dma_htrans];
world[dma_hwrite]    -> swerv[dma_hwrite];
world[dma_hwdata]    -> swerv[dma_hwdata];
world[dma_hsel]      -> swerv[dma_hsel];
world[dma_hreadyin]  -> swerv[dma_hreadyin];

swerv[dma_hrdata]    -> world[dma_hrdata];
swerv[dma_hreadyout] -> world[dma_hreadyout];
swerv[dma_hresp]     -> world[dma_hresp];

world[lsu_bus_clk_en] -> swerv[lsu_bus_clk_en];
world[ifu_bus_clk_en] -> swerv[ifu_bus_clk_en];
world[dbg_bus_clk_en] -> swerv[dbg_bus_clk_en];
world[dma_bus_clk_en] -> swerv[dma_bus_clk_en];

// ### Misc

world[extintsrc_req] -> swerv[extintsrc_req];
world[timer_int]     -> swerv[timer_int];

// ## Connecting the `mem`.

swerv[core_rst_l] -> mem[rst_l];

swerv[lsu_freeze_dc3]           -> mem[lsu_freeze_dc3];
swerv[dccm_clk_override]        -> mem[dccm_clk_override];
swerv[icm_clk_override]         -> mem[icm_clk_override];

swerv[dec_tlu_core_ecc_disable] -> mem[dec_tlu_core_ecc_disable];


// ### DCCM ports
swerv[dccm_wren] -> mem[dccm_wren];
swerv[dccm_rden] -> mem[dccm_rden];

swerv[dccm_wr_addr]    -> mem[dccm_wr_addr];
swerv[dccm_rd_addr_lo] -> mem[dccm_rd_addr_lo];
swerv[dccm_rd_addr_hi] -> mem[dccm_rd_addr_hi];
swerv[dccm_wr_data]    -> mem[dccm_wr_data];

mem[dccm_rd_data_lo] -> swerv[dccm_rd_data_lo];
mem[dccm_rd_data_hi] -> swerv[dccm_rd_data_hi];

// ### ICCM ports
swerv[iccm_rw_addr] -> mem[iccm_rw_addr];
swerv[iccm_wren]    -> mem[iccm_wren];
swerv[iccm_rden]    -> mem[iccm_rden];
swerv[iccm_wr_size] -> mem[iccm_wr_size];
swerv[iccm_wr_data] -> mem[iccm_wr_data];

mem[iccm_rd_data]   -> swerv[iccm_rd_data];

// ### Icache and Itag Ports

swerv[ic_rw_addr]         -> mem[ic_rw_addr];
swerv[ic_tag_valid]       -> mem[ic_tag_valid];
swerv[ic_wr_en]           -> mem[ic_wr_en];
swerv[ic_rd_en]           -> mem[ic_rd_en];
swerv[ic_premux_data]     -> mem[ic_premux_data];
swerv[ic_sel_premux_data] -> mem[ic_sel_premux_data];
swerv[ic_wr_data]         -> mem[ic_wr_data];
swerv[ic_debug_wr_data]   -> mem[ic_debug_wr_data];


swerv[ic_debug_rd_en]     -> mem[ic_debug_rd_en];
swerv[ic_debug_wr_en]     -> mem[ic_debug_wr_en];
swerv[ic_debug_tag_array] -> mem[ic_debug_tag_array];
swerv[ic_debug_way]       -> mem[ic_debug_way];

swerv[ic_debug_addr] -> mem[ic_debug_addr];

mem[ic_rd_data]          -> swerv[ic_rd_data];
mem[ictag_debug_rd_data] -> swerv[ictag_debug_rd_data];
mem[ic_rd_hit]           -> swerv[ic_rd_hit];
mem[ic_tag_perr]         -> swerv[ic_tag_perr];

// ## Connecting the `dmi_wrapper`.

// JTAG signals
world[jtag_trst_n] -> dmi_wrapper[trst_n]; // JTAG reset
world[jtag_tck]    -> dmi_wrapper[tck];    // JTAG clock
world[jtag_tms]    -> dmi_wrapper[tms];    // Test mode select
world[jtag_tdi]    -> dmi_wrapper[tdi];    // Test Data Input
dmi_wrapper[tdo]   -> world[jtag_tdo];     // Test Data Output

// Processor Signals

world[jtag_id]              -> dmi_wrapper[jtag_id];   // 32 bit JTAG ID
swerv[dmi_reg_rdata]        -> dmi_wrapper[rd_data];   // 32 bit Read data from  Processor
dmi_wrapper[reg_wr_data]    -> swerv[dmi_reg_wdata];   // 32 bit Write data to Processor
dmi_wrapper[reg_wr_addr]    -> swerv[dmi_reg_addr];    // 32 bit Write address to Processor
dmi_wrapper[reg_en]         -> swerv[dmi_reg_en];      // 1 bit  Write enable to Processor
dmi_wrapper[reg_wr_en]      -> swerv[dmi_reg_wr_en];
dmi_wrapper[dmi_hard_reset] -> swerv[dmi_hard_reset];  //a hard reset of the DTM, causing the DTM to forget about any

// End of Model.
