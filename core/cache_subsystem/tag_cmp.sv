// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distDCACHE_TAG_WIDTH_SRAMributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
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
    parameter type                   l_data_SRAM_t         = std_cache_pkg::cache_line_SRAM_t,
    parameter type                   l_be_t           = std_cache_pkg::cl_be_t,
    parameter type                   l_be_SRAM_t           = std_cache_pkg::cl_be_SRAM_t,
    parameter int unsigned           DCACHE_SET_ASSOC = 8,
    parameter  int unsigned NumRMWCuts       = 0, // Number of cuts in the read-modify-write path
    parameter type reg_req_t = logic,
    parameter type reg_rsp_t = logic

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
    output logic error_inc_o,

    output logic    [DCACHE_SET_ASSOC-1:0] req_o,
    output logic    [      ADDR_WIDTH-1:0] addr_o,
    output l_data_SRAM_t                        wdata_o,
    output logic                           we_o,
    output l_be_SRAM_t                          be_o,
    input  l_data_SRAM_t [DCACHE_SET_ASSOC-1:0] rdata_i, 

    input vldrty_ECC_t [DCACHE_SET_ASSOC-1:0] dirty_rdata_i,
    output vldrty_ECC_t [DCACHE_SET_ASSOC-1:0] be_valid_dirty_ram_o,
    output vldrty_ECC_t [DCACHE_SET_ASSOC-1:0] wdata_dirty_o
);

vldrty_t [DCACHE_SET_ASSOC-1:0] dirty_rdata;
     vldrty_t [DCACHE_SET_ASSOC-1:0] be_valid_dirty_ram;
     vldrty_t [DCACHE_SET_ASSOC-1:0] wdata_dirty;

     vldrty_ECC_t [DCACHE_SET_ASSOC-1:0] dirty_rdata2;
     vldrty_ECC_t [DCACHE_SET_ASSOC-1:0] be_valid_dirty_ram2;
     vldrty_t [DCACHE_SET_ASSOC-1:0] wdata_dirty2;

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
  l_data_SRAM_t                         wdata_scrub;
  l_data_t to_store, wdata;
  
  logic [DCACHE_LINE_WIDTH-1:0] to_store_data;
  logic [DCACHE_LINE_WIDTH-1:0] sel_loaded_data;
  logic [DCACHE_TAG_WIDTH-1:0] sel_loaded_tag;
  l_data_t input_buffer, output_buffer;
  l_data_SRAM_t input_buffer_d, input_buffer_q;

  //rdata
  l_data_SRAM_t [DCACHE_SET_ASSOC-1:0] rdata;
  logic [DCACHE_SET_ASSOC-1:0][DCACHE_LINE_WIDTH-1:0] loaded;




  //be
  l_be_t be_buffer_d, be_buffer_q;//TODO make ECC
  l_be_SRAM_t be;

  logic [DCACHE_LINE_WIDTH-1:0] be_selector_data;  
  logic [DCACHE_TAG_WIDTH-1:0] be_selector_tag; 

  // error
  logic [DCACHE_SET_ASSOC-1:0][SECDEC_DIVISIONS_DATA-1:0][1:0] err_data;
  logic [DCACHE_SET_ASSOC-1:0][1:0] err_tag, err_vldrty;
  logic [SECDEC_DIVISIONS_DATA-1:0][1:0] err_input_buffer;
  logic [1:0] err_input_tag;


  assign be_selector_data    = {{8{be_buffer_q.data[15]}},{8{be_buffer_q.data[14]}},
                           {8{be_buffer_q.data[13]}},{8{be_buffer_q.data[12]}},
                           {8{be_buffer_q.data[11]}},{8{be_buffer_q.data[10]}},
                           {8{be_buffer_q.data[9]}},{8{be_buffer_q.data[8]}},
                           {8{be_buffer_q.data[7]}},{8{be_buffer_q.data[6]}},
                           {8{be_buffer_q.data[5]}},{8{be_buffer_q.data[4]}},
                           {8{be_buffer_q.data[3]}},{8{be_buffer_q.data[2]}},
                           {8{be_buffer_q.data[1]}},{8{be_buffer_q.data[0]}}}; // how I understand this, it checks which bytes of the buffershould be selected, if cacheline changes this must too


  assign be_selector_tag    = {{4{be_buffer_q.tag[5]}},{8{be_buffer_q.tag[4]}},
                           {8{be_buffer_q.tag[3]}},{8{be_buffer_q.tag[2]}},
                           {8{be_buffer_q.tag[1]}},{8{be_buffer_q.tag[0]}}};

                          

  vldrty_t [DCACHE_SET_ASSOC-1:0] a;
  vldrty_t [DCACHE_SET_ASSOC-1:0] b;
  for (genvar i = 0; i < DCACHE_SET_ASSOC; i++) begin

    assign be_valid_dirty_ram[i].valid = be_o.vldrty[i].valid;
    assign be_valid_dirty_ram[i].dirty = be_o.vldrty[i].dirty;


    assign wdata_dirty[i].dirty              = store_state_q == NORMAL ? wdata.dirty : input_buffer_q.dirty;;
    assign wdata_dirty[i].valid              = store_state_q == NORMAL ? wdata.valid : input_buffer_q.valid;;


    assign rdata_o[i].dirty          = dirty_rdata[i].dirty;
    assign rdata_o[i].valid          = dirty_rdata[i].valid;
        


  end
  // TODO make ECC
  assign wdata_dirty2 = (be_valid_dirty_ram& wdata_dirty) | (~be_valid_dirty_ram& dirty_rdata);
  assign dirty_rdata2 = dirty_rdata_i;
  for (genvar i = 0; i<DCACHE_SET_ASSOC; i++)begin
      assign be_valid_dirty_ram_o[i] = store_state_q==NORMAL ? (be_valid_dirty_ram[i]=='0 ? '0 : '1) : '1 ; // TODO check if makes sense

  end



  // one hot encoded
  logic [NR_PORTS-1:0] id_d, id_q;
  logic [ariane_pkg::DCACHE_TAG_WIDTH-1:0] sel_tag;
  logic [DCACHE_TAG_WIDTH_SRAM-1:0] sel_tag_SRAM;

  always_comb begin : tag_sel
    sel_tag = '0;
    for (int unsigned i = 0; i < NR_PORTS; i++) if (id_q[i]) sel_tag = tag_i[i];
  end




  if (SECDEC_ENABLED) begin

    // read 
    for (genvar i = 0; i<DCACHE_SET_ASSOC; i++)begin : rdata_copy

      hsiao_ecc_dec_wrap #(
        .DIVISIONS(1),
        .ASSOC(1),
        .SIZE( DCACHE_TAG_WIDTH)
      ) ecc_input_wrap (
        .data_i(rdata[i].tag),
        .data_o(rdata_o[i].tag),
        .err_o(err_tag[i])
      );

      hsiao_ecc_dec_wrap #(
        .DIVISIONS(SECDEC_DIVISIONS_DATA),
        .ASSOC(1),
        .SIZE(DCACHE_LINE_WIDTH)
      ) ecc_rtag_dec_wrap (
        .data_i(rdata[i].data),
        .data_o(loaded[i]),
        .err_o(err_data[i])
      );

    
      assign rdata_o[i].data   = loaded[i];
    end

    always_comb begin
      sel_loaded_data = '0;
      sel_loaded_tag = '0;

      for (int unsigned i = 0; i< DCACHE_SET_ASSOC; i++) if (req_buffer_q[i]) begin
        sel_loaded_data=rdata_o[i].data;
        sel_loaded_tag=rdata_o[i].tag;
        break;
      end

    end


    always_comb begin 
      to_store_data ='0;
      for (int unsigned i = 0; i< DCACHE_LINE_WIDTH; i++)begin
        if (to_store.data[i]==1'b1)begin
          to_store_data[i] = 1'b1;
        end
      end

    end
    // write



    hsiao_ecc_enc_wrap #(
      .DIVISIONS(SECDEC_DIVISIONS_DATA),
      .ASSOC(1),
      .SIZE(DCACHE_LINE_WIDTH)
    ) ecc_wdata_wrap (
      .data_i(to_store_data),
      .data_o(wdata_scrub.data)
    );

    hsiao_ecc_enc_wrap #(
      .DIVISIONS(1),
      .ASSOC(1),
      .SIZE(DCACHE_TAG_WIDTH)
    ) ecc_wtag_wrap (
      .data_i(to_store.tag),
      .data_o(wdata_scrub.tag)
    );

    assign to_store.data = store_state_q == NORMAL ? wdata.data : (be_selector_data & output_buffer.data) | (~be_selector_data & sel_loaded_data); // take the bits from the input which should be written and otherwise take the stored values
    assign to_store.tag = store_state_q == NORMAL ? wdata.tag : (be_selector_tag & output_buffer.tag) | (~be_selector_tag & sel_loaded_tag);

    hsiao_ecc_dec_wrap #(
      .DIVISIONS(1),
      .ASSOC(DCACHE_SET_ASSOC),
      .SIZE( $bits(vldrty_t))
    ) ecc_input_wrap (
      .data_i(dirty_rdata2),
      .data_o(dirty_rdata),
      .err_o(err_vldrty)
    );


    hsiao_ecc_enc_wrap #(
      .DIVISIONS(1),
      .ASSOC(DCACHE_SET_ASSOC),
      .SIZE($bits(vldrty_t))
    ) ecc_wdirty_wrap (
      .data_i(wdata_dirty2),
      .data_o(wdata_dirty_o)
    );

    hsiao_ecc_enc_wrap #(
      .DIVISIONS(1),
      .ASSOC(1),
      .SIZE(DCACHE_TAG_WIDTH)
    ) ecc_stag_wrap (
      .data_i(sel_tag),
      .data_o(sel_tag_SRAM)
    );

    hsiao_ecc_dec_wrap #(
        .DIVISIONS(SECDEC_DIVISIONS_DATA),
        .ASSOC(1),
        .SIZE(DCACHE_LINE_WIDTH)
      ) ecc_input_data_dec_wrap (
        .data_i(input_buffer_q.data),
        .data_o(output_buffer.data),
        .err_o(err_input_buffer)
      );

    
    hsiao_ecc_dec_wrap #(
        .DIVISIONS(1),
        .ASSOC(1),
        .SIZE(DCACHE_TAG_WIDTH)
      ) ecc_input_tag_wrap (
        .data_i(input_buffer_q.tag),
        .data_o(output_buffer.tag),
        .err_o(err_input_tag)
      );




    logic [DCACHE_TAG_WIDTH_SRAM-1:0] input_buffer_tag;
    logic [DCACHE_LINE_WIDTH_SRAM-1:0] input_buffer_data;
    logic [DCACHE_LINE_WIDTH-1:0] input_buffer_data_full;

    hsiao_ecc_enc_wrap #(
      .DIVISIONS(1),
      .ASSOC(1),
      .SIZE(DCACHE_TAG_WIDTH)
    ) ecc_wtag_input_wrap (
      .data_i(input_buffer.tag),
      .data_o(input_buffer_tag)
    );

    hsiao_ecc_enc_wrap #(
      .DIVISIONS(SECDEC_DIVISIONS_DATA),
      .ASSOC(1),
      .SIZE(DCACHE_LINE_WIDTH)
    ) ecc_wdata_input_wrap (
      .data_i(input_buffer_data_full),
      .data_o(input_buffer_data)
    );



    always_comb begin
          input_buffer_data_full ='0;
      for (int unsigned i = 0; i< DCACHE_LINE_WIDTH; i++)begin
        if (input_buffer.data[i]==1'b1)begin
          input_buffer_data_full[i] = 1'b1;
        end
      end
      if (store_state_q == NORMAL) begin
        input_buffer_d.valid = input_buffer.valid;
        input_buffer_d.dirty = input_buffer.dirty;
        input_buffer_d.data = input_buffer_data;
        input_buffer_d.tag = input_buffer_tag;
      end
      else begin
        input_buffer_d = input_buffer_q;
      end
    end
  end
  else begin
    assign wdata_scrub = wdata;
    assign rdata_o = rdata;

    assign dirty_rdata = dirty_rdata2;
    assign wdata_dirty_o = wdata_dirty2;

    assign sel_tag_SRAM = sel_tag;
    assign input_buffer_d = (store_state_q == NORMAL)? input_buffer: input_buffer_q;

  end


  logic [DCACHE_SET_ASSOC-1:0][DCACHE_TAG_WIDTH_SRAM-1:0] tag_xor;
  for (genvar j = 0; j < DCACHE_SET_ASSOC; j++) begin : tag_cmp
    assign tag_xor[j] = sel_tag_SRAM ^ rdata_i[j].tag;

    assign hit_way_o[j] = ((tag_xor[j] & (tag_xor[j]-1))==0) ? rdata_o[j].valid : 1'b0; //TODO make rdata_i, 
  end


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


        we     = we_i[i];
        wdata  = wdata_i[i];

        // Store in buffer in case of load and store
        be_buffer_d = be_i[i];
        add_buffer_d = addr_i[i];
        input_buffer = wdata_i[i];
        req_buffer_d = req_i[i];
        if (SECDEC_ENABLED) begin
          be.tag     = (be_i[i].tag=='0)? '0 : '1;
          be.data    = '0; 
          be.vldrty  = be_i[i].vldrty;
          for (int unsigned j=0; j<SECDEC_DIVISIONS_DATA; j++)begin
              if (be_i[i].data[j*SECDEC_BLOCK_SIZE/8+:SECDEC_BLOCK_SIZE/8] != '0)begin
                be.data[j] = 1'b1;
              end
              if (SECDEC_ENABLED && (|req_i[i]) & (be_i[i].data[j*SECDEC_BLOCK_SIZE/8+:SECDEC_BLOCK_SIZE/8] !='0 && be_i[i].data[j*SECDEC_BLOCK_SIZE/8+:SECDEC_BLOCK_SIZE/8] != '1)  & we_i[i]) begin 
                store_state_d = LOAD_AND_STORE; // write requests which need another cycle
                we = 1'b0;
                gnt_o[i] = 1'b0;
              end
          end

        
          // & (be_i[i].vldrty !='0 && be_i[i].vldrty != '1) 
          for (int unsigned j=0; j<DCACHE_SET_ASSOC; j++)begin
            if (SECDEC_ENABLED && (|req_i[i]) & (be_i[i].vldrty[j] !='0 && be_i[i].vldrty[j] != '1)  & we_i[i]) begin 
              store_state_d = LOAD_AND_STORE; // write requests which need another cycle
              we = 1'b0;
              gnt_o[i] = 1'b0;
            end
          end

        end
        else begin
          be = be_i[i];
          
        end
        if (|req_i[i]) break;
      
      end
    end
    else begin // happens only if SECDEC_ENABLED
      addr = add_buffer_q;
      we = 1'b1;
      //input_buffer_d = input_buffer_q;
      add_buffer_d = add_buffer_q;
      for (int unsigned i=0; i<NR_PORTS; i++) begin
        if (id_q[i] == 1'b1) begin
          gnt_o[i] = 1'b1;
        end
      end
      be.data = '0; 
      be.tag = (be_buffer_q.tag=='0)? '0 : '1; // set to 1 bc alwazs read/write whole tag
      be.vldrty = be_buffer_q.vldrty;

      for (int unsigned j=0; j<SECDEC_DIVISIONS_DATA; j++)begin
            if (be_buffer_q.data[j*SECDEC_BLOCK_SIZE/8+:SECDEC_BLOCK_SIZE/8] != '0)begin
              be.data[j] = '1;
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


  logic [1:0] err_scrub; 
  if (SECDEC_ENABLED) begin

      
      ecc_scrubber_cache #(
        .BankSize       ( 2**(DCACHE_INDEX_WIDTH-DCACHE_BYTE_OFFSET)       ), 
        .UseExternalECC ( 0              ),
        .WITH_VALID(1),
        .Assoc(DCACHE_SET_ASSOC),
        .TagWidth(DCACHE_TAG_WIDTH),
        .BlockWidth(SECDEC_BLOCK_SIZE),
        .BlockWidthECC(SECDEC_BLOCK_SIZE_ECC),
        .DataDivisions(SECDEC_DIVISIONS_DATA),
        .be_t(std_cache_pkg::cl_be_SRAM_t),
        .line_t(std_cache_pkg::cache_line_SRAM_t)
      ) i_scrubber (
        .clk_i,
        .rst_ni,

        .scrub_trigger_i ( 1'b1),
        .bit_corrected_o (err_scrub[0]),
        .uncorrectable_o (err_scrub[1]),

        .intc_req_i      ( req         ),
        .intc_we_i       ( we          ),
        .intc_add_i      ( addr[DCACHE_INDEX_WIDTH-1:DCACHE_BYTE_OFFSET]         ),
        .intc_wdata_i    ( wdata_scrub       ),
        .intc_rdata_o    ( rdata       ),
        .intc_be_i 	  (be),

        .bank_req_o      ( req_o   ),
        .bank_we_o       (  we_o   ),
        .bank_add_o      (  addr_o[DCACHE_INDEX_WIDTH-1:DCACHE_BYTE_OFFSET] ),
        .bank_wdata_o    ( wdata_o),
        .bank_rdata_i    ( rdata_i ),
        .bank_be_o ( be_o),



        .ecc_err_i('1),
        .ecc_in_i('1),
        .ecc_out_o()
      );

  end else begin
    assign req_o = req;
    assign we_o = we;
    assign addr_o = addr;
    assign wdata_o = wdata_scrub;
    assign rdata = rdata_i;
    assign be_o = be;
  end


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      id_q <= 0;
      store_state_q  <= NORMAL;
      add_buffer_q   <= '0;
      input_buffer_q <= '0;
      be_buffer_q    <= '0;
      req_buffer_q    <= '0;
    end else begin
      id_q <= id_d;
      add_buffer_q   <= add_buffer_d;
      store_state_q  <= store_state_d;
      input_buffer_q <= input_buffer_d;
      be_buffer_q    <= be_buffer_d;
      req_buffer_q   <= req_buffer_d;

     //if (be_valid_dirty_ram!='0 && we_o) begin
      //  $display(1, "BE: %x, DATA: %x, STATE=%x, LOADED: %x", be_valid_dirty_ram_o, wdata_dirty_o, store_state_q, dirty_rdata_i);
      //end
    end
  end
  
  //  1) scrubber 2) read tag 3) read data 4) read vldrty 5) buffer data 6) buffer tag
  logic [5:0] correctable;
  logic [5:0] uncorrectable;
  
  assign correctable[0] = err_scrub[0];
  assign uncorrectable[0] = err_scrub[1];
  


  always_comb begin
    for (int unsigned i = 0; i<DCACHE_SET_ASSOC; i++)begin
        if (err_tag[i][0] && rdata_o[i].valid) begin
          $display("1", "rr %d ", i);
          correctable[1] = 1'b1;
        end
        if (err_tag[i][1] && rdata_o[i].valid) begin
          
          $display("1", "rm %d %d", i,i);
          uncorrectable[1] = 1'b1;
        end
        for (int unsigned j = 0; j < SECDEC_DIVISIONS_DATA;j++) begin
          if (err_data[i][j][0] && rdata_o[i].valid) begin
          $display("1", "mr %d %d", i,j);
          correctable[2] = 1'b1;
          end
          if (err_data[i][j][1] && rdata_o[i].valid) begin
            $display("1", "mm %d %d", i,j);
            uncorrectable[2] = 1'b1;
          end
        end

        if (err_vldrty[i][0]) begin
          $display("1", "vldr 0");
          correctable[3] = 1'b1;
        end
        if (err_vldrty[i][1]) begin
          $display("1", "vldr 1");
          uncorrectable[3] = 1'b1;
        end


    end

    for (int unsigned j = 0; j<SECDEC_DIVISIONS_DATA;j++) begin
      if (err_input_buffer[j][0]) begin
        correctable[4] = 1'b1;
      end
      if (err_input_buffer[j][1]) begin
        uncorrectable[4] = 1'b1;
      end
      
    end
  end

  assign correctable[5] = err_input_tag[0];
  assign uncorrectable[5] = err_input_tag[1];


  // counters
  logic [6:0][32-1:0] correctable_counters_d,correctable_counters_q;
  logic [6:0][32-1:0] uncorrectable_counters_d,uncorrectable_counters_q;

  always_comb begin
    correctable_counters_d = correctable_counters_q;
    uncorrectable_counters_d = uncorrectable_counters_q;

    for (int i =0; i<6; ++i)begin
      if (correctable[i]) begin
        correctable_counters_d[i] = correctable_counters_q[i]+1;
      end
      if (uncorrectable[i]) begin
        uncorrectable_counters_d[i] = uncorrectable_counters_q[i]+1;
      end
    end

  end

  assign error_inc_o = |uncorrectable; // TODO add previous step and check if it has been read in register
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_counters_un_correctable
    if(~rst_ni) begin
      correctable_counters_q <= 0;
      uncorrectable_counters_q <= 0;
    end else begin
      correctable_counters_q <= correctable_counters_d;
      uncorrectable_counters_q <= uncorrectable_counters_d;
    end
  end




  /*
  ecc_manager #(
    .NumBanks(6),
    .ecc_mgr_req_t( reg_bus_req_t), // need to get from above
    .ecc_mgr_rsp_t(reg_bus_rsp_t)
  ) ecc_manager_errors(
    .clk_i(clk_i),
    .rst_ni(rst_ni),

    .ecc_mgr_req_i('1),
    .ecc_mgr_rsp_o(),

    .bank_faults_i('0),
    .scrub_fix_i(correctable),
    .scrub_uncorrectable_i(uncorrectable),
    .scrub_trigger_o(),
    .test_write_mask_no()
  );*/

endmodule
