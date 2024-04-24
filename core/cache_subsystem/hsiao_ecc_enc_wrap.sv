module hsiao_ecc_enc_wrap
#(
    parameter int unsigned DIVISIONS=1,
    parameter int unsigned ASSOC=1,
    parameter int unsigned SIZE = 1,
    parameter int unsigned BLOCK_SIZE=SIZE/DIVISIONS,
    parameter int unsigned BLOCK_SIZE_ECC = $clog2(BLOCK_SIZE)+BLOCK_SIZE+2,
    parameter int unsigned SIZE_ECC = BLOCK_SIZE_ECC*DIVISIONS

) (
  input logic[ASSOC-1:0][SIZE-1:0] data_i,
  output logic[ASSOC-1:0][SIZE_ECC-1:0] data_o
  
);
  for (genvar i=0; i<ASSOC;i++)begin
    for (genvar j = 0; j<DIVISIONS;j++) begin 
      hsiao_ecc_enc #(
        .DataWidth (BLOCK_SIZE)  
      ) ecc_encode_buffer_data(
        .in(data_i[i][j*BLOCK_SIZE+:BLOCK_SIZE]),
        .out(data_o[i][j*BLOCK_SIZE_ECC+:BLOCK_SIZE_ECC])

      );
    end
  end

endmodule