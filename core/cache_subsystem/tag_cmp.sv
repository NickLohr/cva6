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
module tag_cmp #(
    parameter config_pkg::cva6_cfg_t CVA6Cfg          = config_pkg::cva6_cfg_empty,
    parameter int unsigned           NR_PORTS         = 3,
    parameter int unsigned           ADDR_WIDTH       = 64,
    parameter type                   l_data_t         = std_cache_pkg::cache_line_t,
    parameter type                   l_data_ECC_t     = std_cache_pkg::cache_line_ECC_t,
    parameter type                   l_be_t           = std_cache_pkg::cl_be_t,
    parameter type                   l_be_ECC_t      = std_cache_pkg::cl_be_ECC_t,
    parameter int unsigned           DCACHE_SET_ASSOC = 8
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


    output logic    [DCACHE_SET_ASSOC-1:0]      req_o,
    output logic    [      ADDR_WIDTH-1:0]      addr_o,
    output l_data_ECC_t                         wdata_o,
    output logic                                we_o,
    output l_be_ECC_t                               be_o, // TODO next
    input  l_data_ECC_t [DCACHE_SET_ASSOC-1:0]  rdata_i
);

  l_data_t wdata;
  l_be_t be;
  logic [DCACHE_SET_ASSOC-1:0][1:0] err;
   
  
  for (genvar i = 0; i<DCACHE_SET_ASSOC; i++)begin : rdata_copy
    assign rdata_o[i].valid = rdata_i[i].valid;
    assign rdata_o[i].tag = rdata_i[i].tag;
    assign rdata_o[i].dirty = rdata_i[i].dirty;

    for (genvar j = 0; j<((DCACHE_LINE_WIDTH+7)/8);j++){
      hsiao_ecc_dec #(.DataWidth(8)
      ) i_hsio_ecc_dec_rdata (
        .in(rdata_i[i].data[j*13+:13]),
        .out(rdata_o[i].data[j*8+:8]),
        .syndrome_o(),
        .err_o(err[i]) // TODO error handling

    
  

    );

    }


    
    /* No correction, just rewiring

    hsiao_ecc_dec #(.DataWidth(ariane_pkg::DCACHE_LINE_WIDTH)
    ) i_hsio_ecc_dec_rdata (
      .in(rdata_i[i].data),
      .out(rdata_o[i].data),
      .syndrome_o(),
      .err_o(err[i]) // TODO error handling

  
  

    );*/
  end
  for (genvar j = 0; j<((DCACHE_LINE_WIDTH+7)/8);j++){
    hsiao_ecc_enc #(.DataWidth(8)
    ) i_hsio_ecc_enc_wdata (
      .in(wdata.data[j*8+:8]),
      .out(wdata_o.data[j*13+:13])
    );
  }

  assign wdata_o.valid = wdata.valid;
  assign wdata_o.tag = wdata.tag;
  assign wdata_o.dirty = wdata.dirty;


  assign be_o.vldrty = be.vldrty;
  assign be_o.data= be.data;
  assign be_o.tag = be.tag;

  // one hot encoded
  logic [NR_PORTS-1:0] id_d, id_q;
  logic [ariane_pkg::DCACHE_TAG_WIDTH-1:0] sel_tag;

  always_comb begin : tag_sel
    sel_tag = '0;
    for (int unsigned i = 0; i < NR_PORTS; i++) if (id_q[i]) sel_tag = tag_i[i];
  end

  for (genvar j = 0; j < DCACHE_SET_ASSOC; j++) begin : tag_cmp
    assign hit_way_o[j] = (sel_tag == rdata_i[j].tag) ? rdata_i[j].valid : 1'b0;
  end

  always_comb begin

    gnt_o   = '0;
    id_d    = '0;
    wdata = '0;
    req_o   = '0;
    addr_o  = '0;
    be    = '0;
    we_o    = '0;
    // Request Side
    // priority select
    // TODO does it make sense to put things in if statement?
    for (int unsigned i = 0; i < NR_PORTS; i++) begin
      req_o    = req_i[i];
      id_d     = (1'b1 << i);
      gnt_o[i] = 1'b1;
      addr_o   = addr_i[i];
      be      = be_i[i];
      we_o     = we_i[i];
      wdata    = wdata_i[i];

      if (req_i[i]) break;
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



  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      id_q <= 0;
    end else begin
      id_q <= id_d;
    end
  end


endmodule
