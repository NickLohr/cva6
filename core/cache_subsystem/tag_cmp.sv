// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// --------------
// Tag Compare
// --------------
//
// Description: Arbitrates access to cache memories, simplified request grant protocol
//              checks for hit or miss on cache
//
module tag_cmp 
  import std_cache_pkg::*;
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg          = config_pkg::cva6_cfg_empty,
    parameter int unsigned           NR_PORTS         = 3,
    parameter int unsigned           ADDR_WIDTH       = 64,
    parameter type                   l_data_t         = std_cache_pkg::cache_line_t,
    parameter type                   l_data_ECC_t         = std_cache_pkg::cache_line_ECC_t,
    parameter type                   l_be_t           = std_cache_pkg::cl_be_t,
    parameter type                   l_be_ECC_t           = std_cache_pkg::cl_be_ECC_t,
    parameter int unsigned           DCACHE_SET_ASSOC = 8,
    parameter  int unsigned NumRMWCuts       = 0 // Number of cuts in the read-modify-write path
   ) (
    input logic clk_i,
    input logic rst_ni,

    input logic [NR_PORTS-1:0][DCACHE_SET_ASSOC-1:0] req_i,
    output logic [NR_PORTS-1:0] gnt_o,
    input logic [NR_PORTS-1:0][ADDR_WIDTH-1:0] addr_i,
    input l_data_t [NR_PORTS-1:0] wdata_i,
    input logic [NR_PORTS-1:0] we_i,
    input l_be_t [NR_PORTS-1:0] be_i,
    output l_data_t [DCACHE_SET_ASSOC-1:0] rdata_o,
    input  logic    [NR_PORTS-1:0][ariane_pkg::DCACHE_TAG_WIDTH-1:0] tag_i, // tag in - comes one cycle later
    output logic [DCACHE_SET_ASSOC-1:0] hit_way_o,  // we've got a hit on the corresponding way


    output logic    [DCACHE_SET_ASSOC-1:0] req_o,
    output logic    [      ADDR_WIDTH-1:0] addr_o,
    output l_data_ECC_t                        wdata_o,
    output logic                           we_o,
    output l_be_ECC_t                          be_o,
    input  l_data_ECC_t [DCACHE_SET_ASSOC-1:0] rdata_i
);

  //assign rdata_o = rdata_i;
  typedef enum logic { NORMAL, LOAD_AND_STORE } store_state_e;
  store_state_e store_state_d, store_state_q;

  //req
  logic    [DCACHE_SET_ASSOC-1:0] req;
    logic    [DCACHE_SET_ASSOC-1:0] req_buffer_d, req_buffer_q;

  // addr
  logic    [      ADDR_WIDTH-1:0] addr;
    logic [ADDR_WIDTH-1:0] add_buffer_d, add_buffer_q;


  //we
  logic                           we;

  //wdata
  l_data_ECC_t                         wdata_srub;
  l_data_t to_store, wdata;
  
  logic [DCACHE_LINE_WIDTH-1:0] to_store_data;
  logic [DCACHE_LINE_WIDTH-1:0] sel_loaded;
  l_data_t input_buffer_d, input_buffer_q;

  //rdata
  l_data_ECC_t [DCACHE_SET_ASSOC-1:0] decoder_in, rdata;
  logic [DCACHE_SET_ASSOC-1:0][DCACHE_LINE_WIDTH-1:0] loaded;
  l_data_t [DCACHE_SET_ASSOC-1:0] rdata_buffer_d, rdata_buffer_q;




  //be
  l_be_ECC_t be_buffer_d, be_buffer_q;
  l_be_ECC_t be;

  logic [DCACHE_LINE_WIDTH-1:0] be_selector; 

  // error
    logic [DCACHE_SET_ASSOC-1:0][SECDEC_DIVISIONS_DATA-1:0][1:0] err_data;



  assign be_selector    = {{8{be_buffer_q.data[15]}},{8{be_buffer_q.data[14]}},
                           {8{be_buffer_q.data[13]}},{8{be_buffer_q.data[12]}},
                           {8{be_buffer_q.data[11]}},{8{be_buffer_q.data[10]}},
                           {8{be_buffer_q.data[9]}},{8{be_buffer_q.data[8]}},
                           {8{be_buffer_q.data[7]}},{8{be_buffer_q.data[6]}},
                           {8{be_buffer_q.data[5]}},{8{be_buffer_q.data[4]}},
                           {8{be_buffer_q.data[3]}},{8{be_buffer_q.data[2]}},
                           {8{be_buffer_q.data[1]}},{8{be_buffer_q.data[0]}}}; // how I understand this, it checks which bytes of the buffershould be selected, if cacheline changes this must too

  assign decoder_in = store_state_q == NORMAL ? rdata : rdata;


  for (genvar i = 0; i<DCACHE_SET_ASSOC; i++)begin : rdata_copy

    assign rdata_o[i].valid = rdata[i].valid; // TODO improve error handling ((|err_data[i])[1]) ? '0 :
    assign rdata_o[i].dirty = rdata[i].dirty;
    assign rdata_o[i].tag   = rdata[i].tag;


    for (genvar j = 0; j<SECDEC_DIVISIONS_DATA;j++) begin 
      hsiao_ecc_dec #(.DataWidth(SECDEC_BLOCK_SIZE)
      ) i_hsio_ecc_dec_rdata (
        .in(decoder_in[i].data[j*SECDEC_BLOCK_SIZE_ECC+:SECDEC_BLOCK_SIZE_ECC]),
        .out(loaded[i][j*SECDEC_BLOCK_SIZE+:SECDEC_BLOCK_SIZE]),
        .syndrome_o(),
        .err_o(err_data[i][j]) // TODO error handling, look in wrapper for info how to
      );
    
    end
   assign rdata_o[i].data   = loaded[i];

   end
    assign rdata_buffer_d = rdata_o;

   always_comb begin
    sel_loaded = '0;
    for (int unsigned i = 0; i< DCACHE_SET_ASSOC; i++) if (req_buffer_q[i]) begin
      sel_loaded=loaded[i];
      break;
    end

  end
    assign to_store.data = store_state_q == NORMAL ? wdata.data : (be_selector & input_buffer_q.data) | (~be_selector & sel_loaded); // take the bits from the input which should be written and otherwise take the stored values
  
  always_comb begin
    to_store_data ='0;
    for (int unsigned i = 0; i< DCACHE_LINE_WIDTH; i++)begin
      if (to_store.data[i]==1'b1)begin
        to_store_data[i] = 1'b1;
      end
    end

  end
  for (genvar j=0; j<SECDEC_DIVISIONS_DATA;j++)begin
    hsiao_ecc_enc #(
      .DataWidth (SECDEC_BLOCK_SIZE)
      
    ) ecc_encode (
      .in  (to_store_data[j*SECDEC_BLOCK_SIZE+:SECDEC_BLOCK_SIZE]  ),
      .out ( wdata_srub.data[j*SECDEC_BLOCK_SIZE_ECC+:SECDEC_BLOCK_SIZE_ECC] )
    );

  end
  assign wdata_srub.tag = store_state_q == NORMAL ? wdata.tag : input_buffer_q.tag;
  assign wdata_srub.dirty = store_state_q == NORMAL ? wdata.dirty : input_buffer_q.dirty;
  assign wdata_srub.valid = store_state_q == NORMAL ? wdata.valid : input_buffer_q.valid;


  // one hot encoded
  logic [NR_PORTS-1:0] id_d, id_q;
  logic [ariane_pkg::DCACHE_TAG_WIDTH-1:0] sel_tag;

  always_comb begin : tag_sel
    sel_tag = '0;
    for (int unsigned i = 0; i < NR_PORTS; i++) if (id_q[i]) sel_tag = tag_i[i];
  end

  for (genvar j = 0; j < DCACHE_SET_ASSOC; j++) begin : tag_cmp
    assign hit_way_o[j] = (sel_tag == rdata_i[j].tag) ? rdata_i[j].valid : 1'b0; //rdata_i[j].valid
  end

  logic [SECDEC_BLOCK_SIZE-1:0] ones, zeros;
  logic [SECDEC_BLOCK_SIZE_ECC-1:0] ones_ECC, zeros_ECC;
  assign ones = '1;
  assign ones_ECC = '1;
  assign zeros = '0;

  always_comb begin
    store_state_d = NORMAL;
    gnt_o   = '0;
    id_d    = '0;
    wdata = '0;
    req   = '0;
    addr  = '0;
    be    = '0;
    we    = '0;
    req_buffer_d = req_buffer_q;
    be_buffer_d = be_buffer_q;
    id_d = id_q;
    // Request Side
    // priority select
    if (store_state_q == NORMAL) begin
      for (int unsigned i = 0; i < NR_PORTS; i++) begin
        req    = req_i[i];
        id_d     = (1'b1 << i);
        gnt_o[i] = 1'b1;
        addr   = addr_i[i];
        be.tag     = be_i[i].tag;
        be.data    = '0; // TODO check if right
        be.vldrty  = be_i[i].vldrty;
        we     = we_i[i];
        wdata  = wdata_i[i];

        // Store in buffer in case of load and store
        be_buffer_d = be_i[i];
        add_buffer_d = addr_i[i];
        input_buffer_d = wdata_i[i];
        req_buffer_d = req_i[i];
        for (int unsigned j=0; j<SECDEC_DIVISIONS_DATA; j++)begin
            if (be_i[i].data[j*SECDEC_BLOCK_SIZE+:SECDEC_BLOCK_SIZE] != zeros)begin
              be.data[j*SECDEC_BLOCK_SIZE_ECC+:SECDEC_BLOCK_SIZE_ECC] = ones_ECC;
              //be_buffer_d.data[j*SECDEC_BLOCK_SIZE_ECC+:SECDEC_BLOCK_SIZE_ECC] = ones_ECC;
            end
        end

        // && be_i[i].data[j*SECDEC_BLOCK_SIZE+:SECDEC_BLOCK_SIZE] != 16'b0000_0000_0000_0000
        for (int unsigned j=0; j<SECDEC_DIVISIONS_DATA; j++)begin
          if ((req_i[i]) & (be_i[i].data[j*SECDEC_BLOCK_SIZE+:SECDEC_BLOCK_SIZE] != ones  && be_i[i].data[j*SECDEC_BLOCK_SIZE+:SECDEC_BLOCK_SIZE] != zeros) & we_i[i]) begin // TODO decrease size
            store_state_d = LOAD_AND_STORE; // write requests which need another cycle
            we = 1'b0;

          end
        end
        if (req_i[i]) break;
      
      end
    end
    else begin
      addr = add_buffer_q;
      we = 1'b1;
      input_buffer_d = input_buffer_q;
      add_buffer_d = add_buffer_q;
      be.data = '0; // set all bytes because we are going to write the whole line again TODO change to 32 bit or so 
      be.tag = be_buffer_q.tag;
      be.vldrty = be_buffer_q.vldrty;

      for (int unsigned j=0; j<SECDEC_DIVISIONS_DATA; j++)begin
            if (be_buffer_q.data[j*SECDEC_BLOCK_SIZE+:SECDEC_BLOCK_SIZE] != zeros)begin
              be.data[j*SECDEC_BLOCK_SIZE_ECC+:SECDEC_BLOCK_SIZE_ECC] = ones_ECC;
              //be_buffer_d.data[j*SECDEC_BLOCK_SIZE_ECC+:SECDEC_BLOCK_SIZE_ECC] = ones_ECC;
            end
        end

      req = req_buffer_q;


    end




  

`ifndef SYNTHESIS
`ifndef VERILATOR
    // assert that cache only hits on one way
    // this only needs to be checked one cycle after all ways have been requested
    onehot :
    assert property (@(posedge clk_i) disable iff (!rst_ni) &req_i |=> $onehot0(hit_way_o))
    else begin
      $fatal(1, "Hit should be one-hot encoded");
    end
`endif
`endif
  end

//assign we_o = we;
//assign req_o = req;
//assign addr_o = addr;
//assign wdata_o = wdata_srub;
//assign rdata = rdata_i;





      ecc_scrubber_cache #(
        .BankSize       ( 2**(DCACHE_INDEX_WIDTH-DCACHE_BYTE_OFFSET)       ), 
        .UseExternalECC ( 0              ),
        .DataWidth      ( DCACHE_LINE_WIDTH_ECC ),
        .AddrWidth(DCACHE_INDEX_WIDTH-DCACHE_BYTE_OFFSET),
        .DCACHE_SET_ASSOC(DCACHE_SET_ASSOC)
      ) i_scrubber (
        .clk_i,
        .rst_ni,

        .scrub_trigger_i ( 1'b1  ),
        .bit_corrected_o (    ),
        .uncorrectable_o (  ),

        .intc_req_i      ( req         ),
        .intc_we_i       ( we          ),
        .intc_add_i      ( addr[DCACHE_INDEX_WIDTH-1:DCACHE_BYTE_OFFSET]         ),
        .intc_wdata_i    ( wdata_srub       ),
        .intc_rdata_o    ( rdata       ),
        .intc_be_i (be),

        .bank_req_o      ( req_o   ),
        .bank_we_o       (  we_o   ),
        .bank_add_o      (  addr_o[DCACHE_INDEX_WIDTH-1:DCACHE_BYTE_OFFSET] ),
        .bank_wdata_o    ( wdata_o),
        .bank_rdata_i    ( rdata_i ),
        .bank_be_o ( be_o)
      );




  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      id_q <= 0;
      store_state_q  <= NORMAL;
      add_buffer_q   <= '0;
      input_buffer_q <= '0;
      be_buffer_q    <= '0;
      req_buffer_q    <= '0;
      rdata_buffer_q  <= '0;
    end else begin
      id_q <= id_d;
      add_buffer_q   <= add_buffer_d;
      store_state_q  <= store_state_d;
      input_buffer_q <= input_buffer_d;
      be_buffer_q    <= be_buffer_d;
      req_buffer_q   <= req_buffer_d;
      rdata_buffer_q <= rdata_buffer_d;
    end
  end

endmodule
