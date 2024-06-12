module ecc_external
#(
    parameter int unsigned DIVISIONS=1,
    parameter int unsigned ASSOC=1,
    parameter int unsigned SIZE = 1,
    parameter int unsigned TAG_WIDTH = 1,
    parameter int unsigned BLOCK_SIZE=SIZE/DIVISIONS,
    parameter int unsigned BLOCK_SIZE_ECC = $clog2(BLOCK_SIZE)+BLOCK_SIZE+2,
    parameter int unsigned SIZE_ECC = BLOCK_SIZE_ECC*DIVISIONS,
    parameter type line_t = std_cache_pkg::cache_line_SRAM_t
) (
  input line_t[ASSOC-1:0] data_i,
  output line_t[ASSOC-1:0] data_o,
  output logic[ASSOC-1:0][1:0] err_o
);

  logic[ASSOC-1:0][DIVISIONS-1:0][1:0] err_data;
  logic[ASSOC-1:0]               [1:0] err_tag;
  for (genvar i=0; i<ASSOC;i++)begin
    for (genvar j = 0; j<DIVISIONS;j++) begin 
      hsiao_ecc_cor #(
        .DataWidth (BLOCK_SIZE)  
      ) ecc_encode_buffer_data(
        .in(data_i[i].data[j*BLOCK_SIZE_ECC+:BLOCK_SIZE_ECC]),
        .out(data_o[i].data[j*BLOCK_SIZE_ECC+:BLOCK_SIZE_ECC]),
        .syndrome_o(),
        .err_o(err_data[i][j])

      );
    end
    hsiao_ecc_cor #(
      .DataWidth (TAG_WIDTH)  
    ) ecc_encode_buffer_data(
      .in(data_i[i].tag),
      .out(data_o[i].tag),
      .syndrome_o(),
      .err_o(err_tag[i])

    );   
    assign data_o[i].dirty = data_i[i].dirty;
    assign data_o[i].valid = data_i[i].valid;

    assign err_o[i] = data_i[i].valid ? (|(err_data[i])) | err_tag[i] : '0;
  end
  

endmodule