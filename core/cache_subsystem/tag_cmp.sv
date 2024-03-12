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
    parameter type                   l_data_RAM_t     = std_cache_pkg::cache_line_RAM_t,
    parameter type                   l_be_t           = std_cache_pkg::cl_be_t,
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
    output l_data_RAM_t                         wdata_o,
    output logic                                we_o,
    output l_be_t                               be_o, // TODO next
    input  l_data_RAM_t [DCACHE_SET_ASSOC-1:0]  rdata_i
);

  l_data_t wdata;
  l_be_t be;
  logic [DCACHE_SET_ASSOC-1:0][ariane_pkg::DCACHE_LINE_WIDTH_LENGTH-1:0][1:0] err_data;
  logic [DCACHE_SET_ASSOC-1:0][ariane_pkg::DCACHE_TAG_WIDTH_LENGTH-1:0][1:0] err_tag;

  logic [NR_PORTS:0] id_d, id_q;
  logic change_d, change_q;
  logic [ADDR_WIDTH-1:0] addr_d, addr_q;
  l_data_t corrected_data_d, corrected_data_q;
  logic requested_d, requested_q;

  logic [ariane_pkg::DCACHE_TAG_WIDTH-1:0] sel_tag;
  logic [ariane_pkg::DCACHE_TAG_WIDTH_RAM-1:0] sel_tag_ram;

  
  for (genvar i = 0; i<DCACHE_SET_ASSOC; i++)begin : rdata_copy

    assign rdata_o[i].valid = (err_data[i][1] & be_o[i]) ? '0 : rdata_i[i].valid; // TODO improve error handling (err_data[i][1]) ? '0 :
    assign rdata_o[i].dirty = rdata_i[i].dirty;

    PerByteDecoding #(
      .BYTESIZE(ariane_pkg::BYTESIZE),
      .DataWidth(ariane_pkg::DCACHE_LINE_WIDTH),
      .TotalWidth(ariane_pkg::DCACHE_LINE_WIDTH_RAM)
    ) i_data_read_decoding(
      .data_i(rdata_i[i].data),
      .data_o(rdata_o[i].data), 
      .syndrome_o(),
      .err_o(err_data[i])
    );
    PerByteDecoding #(
      .BYTESIZE(ariane_pkg::BYTESIZE),
      .DataWidth(ariane_pkg::DCACHE_TAG_WIDTH),
      .TotalWidth(ariane_pkg::DCACHE_TAG_WIDTH_RAM)
    ) i_tag_read_decoding(
      .data_i(rdata_i[i].tag),
      .data_o(rdata_o[i].tag), 
      .syndrome_o(),
      .err_o(err_tag[i])
    );

  
   end

  

  PerByteEncoding #(
    .BYTESIZE(ariane_pkg::BYTESIZE),
    .DataWidth(ariane_pkg::DCACHE_TAG_WIDTH),
    .TotalWidth(ariane_pkg::DCACHE_TAG_WIDTH_RAM)
  ) i_encoding_tag(
    .data_i(wdata.tag),
    .data_o(wdata_o.tag)
  );

  PerByteEncoding #(
    .BYTESIZE(ariane_pkg::BYTESIZE),
    .DataWidth(ariane_pkg::DCACHE_LINE_WIDTH),
    .TotalWidth(ariane_pkg::DCACHE_LINE_WIDTH_RAM)
  )i_encoding_data(
    .data_i(wdata.data),
    .data_o(wdata_o.data)
  );

  assign wdata_o.valid = wdata.valid;
  assign wdata_o.dirty = wdata.dirty;

  assign be_o.vldrty = be.vldrty;
  assign be_o.data= be.data;
  assign be_o.tag = be.tag;

  // one hot encoded


  always_comb begin : tag_sel
    sel_tag = '0;
    for (int unsigned i = 0; i < NR_PORTS; i++) if (id_q[i]) sel_tag = tag_i[i];
  end

  
  PerByteEncoding #(
    .BYTESIZE(ariane_pkg::BYTESIZE),
    .DataWidth(ariane_pkg::DCACHE_TAG_WIDTH),
    .TotalWidth(ariane_pkg::DCACHE_TAG_WIDTH_RAM)
  ) i_sel_tag_encoding (
    .data_i(sel_tag),
    .data_o(sel_tag_ram)
  );
  

  for (genvar j = 0; j < DCACHE_SET_ASSOC; j++) begin : tag_cmp
    assign hit_way_o[j] = (sel_tag_ram == rdata_i[j].tag || ariane_pkg::SECDED_ENABLED==0) ? rdata_i[j].valid : 1'b0; 
  end

  always_comb begin

    gnt_o   = '0;
    id_d    = '0;
    wdata = '0;
    req_o   = '0;
    addr_o  = '0;
    be    = '0;
    we_o    = '0;
    corrected_data_d = corrected_data_q;
    change_d = change_q;
    requested_d = requested_q;
    addr_d = addr_q;
    if (requested_q== 1'b1)begin
      addr_d = addr_q+1; // If requested, increase address (would reset if error found)
    end
    


    for (int unsigned i = 0; i < DCACHE_SET_ASSOC; i++)begin
      if (err_data[i][0] && requested_q == 1'b1 && ariane_pkg::SECDED_ENABLED)begin
        corrected_data_d = rdata_o[i]; // TODO future rdata_i
        change_d = 1'b1;
        requested_d = 1'b0;
        addr_d = addr_q; // error found, therefore redo this address
        break;
      end

    end
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
    if (|req_i == 0)begin // TODO add condition from a state when to autocorrect
      // do auto correction 
      req_o = '1; //check if that is correct
      id_d = (1'b1 << NR_PORTS);
      // get to the cache_ctrl which is irrelavant for that
      addr_o = addr_q;
      be.tag = '1;
      be.data = '1;
      be.vldrty = '1; // TODO understand what that does
      we_o = change_q;
      wdata = corrected_data_q; // TODO remove need of encoding in this case
      requested_d = 1'b1;
    end
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
      change_q <= 0;
      addr_q <= 0;
      corrected_data_q <= 0;
      requested_q <= 0;

    end else begin
      id_q <= id_d;
      change_q <= change_d;
      addr_q <= addr_d;
      corrected_data_q <= corrected_data_d;
      requested_q <= requested_d;
    end
  end


endmodule



module PerByteEncoding #(
  parameter int unsigned BYTESIZE = 8,
  parameter int unsigned DataWidth = 64,
  parameter int unsigned DataWidthLength = ((DataWidth+BYTESIZE-1)/BYTESIZE),
  parameter int unsigned TotalWidth = DataWidthLength * ($clog2(BYTESIZE)+2+BYTESIZE)
) (
  input logic[DataWidth-1:0] data_i,
  output logic[TotalWidth-1:0] data_o
);
  logic [TotalWidth-1:0] data; 
  logic[DataWidthLength*BYTESIZE-1:0] upsized;
  for (genvar j = 0; j<DataWidthLength;j++)begin // -1 because it is not precise byte, so the last one just gets calculated smaller
    hsiao_ecc_enc #(.DataWidth(BYTESIZE),
    .TotalWidth(TotalWidth)
    ) i_hsio_ecc_enc_wdata (
      .in(upsized[j*ariane_pkg::BYTESIZE+:ariane_pkg::BYTESIZE]),
      .out(data[j*ariane_pkg::BYTESIZE_RAM+:ariane_pkg::BYTESIZE_RAM])
    );

  end
  always_comb begin
  	upsized = '0;
   	upsized[DataWidth-1:0]= data_i;
  end

  assign data_o = (ariane_pkg::SECDED_ENABLED) ? data : data_i;
endmodule


module PerByteDecoding #(
  parameter int unsigned BYTESIZE = 8,
  parameter int unsigned DataWidth = 64,
  parameter int unsigned DataWidthLength = ((DataWidth+BYTESIZE-1)/BYTESIZE),
  parameter int unsigned TotalWidth = DataWidthLength* ($clog2(BYTESIZE)+2+BYTESIZE),
  parameter int unsigned ProtWidth = ($clog2(BYTESIZE)+2)
)(
  input [TotalWidth-1:0] data_i,
  output [DataWidth-1:0] data_o, 
  output [DataWidthLength-1:0][ProtWidth-1:0] syndrome_o,
  output [DataWidthLength-1:0][1:0] err_o
);
  logic[DataWidthLength*BYTESIZE-1:0] upsized;
  for (genvar j = 0; j<DataWidthLength && ariane_pkg::SECDED_ENABLED;j++) begin
    hsiao_ecc_dec #(.DataWidth(BYTESIZE),
    .TotalWidth(TotalWidth)
    ) i_hsio_ecc_dec_rdata (
      .in(data_i[j*ariane_pkg::BYTESIZE_RAM+:ariane_pkg::BYTESIZE_RAM]),
      .out(upsized[j*ariane_pkg::BYTESIZE+:ariane_pkg::BYTESIZE]),
      .syndrome_o(syndrome_o[j]),
      .err_o(err_o[j]) // TODO error handling
  );
  
  end
assign data_o = (ariane_pkg::SECDED_ENABLED) ? upsized[DataWidth-1:0] : data_i;
endmodule



