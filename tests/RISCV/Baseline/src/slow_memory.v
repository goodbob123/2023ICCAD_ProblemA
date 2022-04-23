// CAwEDSD spring 2017
// slow_memory interface with handshake signal

module slow_memory(
    clk,
    rst_n,
    mem_read,
    mem_write,
    mem_addr,
    mem_wdata,
    mem_rdata,
    mem_ready,
    mem_in,
);
    
    parameter MEM_NUM = 64;
    parameter MEM_WIDTH = 128;
    parameter LATENCY = 15;  // negedge clock after [Unconditional carry(15ns/CYCLE)+1] cycle
        
    parameter IDLE = 2'd0; 
    parameter WAIT = 2'd1; 
    parameter BUBBLE = 2'd2; 
    parameter READY = 2'd3; 
    
    input                  clk, rst_n;
    input                  mem_read, mem_write;
    input           [27:0] mem_addr;
    input  [MEM_WIDTH-1:0] mem_wdata;
    input           [32*MEM_NUM*4-1:0] mem_in;
    output [MEM_WIDTH-1:0] mem_rdata;
    output                 mem_ready;
    
    // internal FF
    reg             [31:0] mem[MEM_NUM*4-1:0];
    reg             [31:0] mem_next[MEM_NUM*4-1:0];
    reg     [1:0]          state, state_next;

    // input FF
    reg                    mem_read_r, mem_write_r;
    reg           [27:0]   mem_addr_r;
    reg  [MEM_WIDTH-1:0]   mem_wdata_r;    

    // output FF
    reg                    mem_ready, mem_ready_next;
    reg    [MEM_WIDTH-1:0] mem_rdata, mem_rdata_next;
    
    integer i, idx, idx2;

    // initial begin
    //     for (idx=0; idx<MEM_NUM*4; idx=idx+1) begin
    //         for (idx2=0; idx2<32; idx2=idx2+1) begin
    //             mem[idx][idx2] = mem_in[idx*32+idx2];
    //         end
    //     end
    // end
    // mem_in = mem;

    always @(posedge clk) begin
        if (!rst_n) {
            for (idx=0; idx<MEM_NUM*4; idx=idx+1) begin
                for (idx2=0; idx2<32; idx2=idx2+1) begin
                    mem[idx][idx2] <= mem_in[idx*32+idx2];
                end
            end
        } else {
            
        }
    end

    always@(*)begin // FSM & control sig
        case(state)
            IDLE:
                begin
                    if(mem_read_r || mem_write_r) begin
                        state_next = WAIT;
                    end
                    else begin
                        state_next = IDLE;
                    end
                    
                    mem_ready_next = 1'b0;
                end
            WAIT:
                begin
                    #(LATENCY);
                    state_next = BUBBLE;
                    mem_ready_next = 1'b0;
                end
            BUBBLE:
                begin
                    // mem_ready PULL UP just 1 cycle
                    state_next = READY;
                    mem_ready_next = 1'b1;
                end
            READY:
                begin
                    state_next = IDLE;  
                    mem_ready_next = 1'b0;                  
                end
            default:
                begin
                    state_next = IDLE;
                    mem_ready_next = 1'b0;
                end     
        endcase
    end
    
    always@(*) begin // Mem array
        for(i=0;i<MEM_NUM*4;i=i+1)
            mem_next[i] = mem[i];
    
        if( state ==  BUBBLE) begin
            if( ~mem_read_r && mem_write_r ) begin
                mem_next[mem_addr_r*4]      = mem_wdata_r[31:0];
                mem_next[mem_addr_r*4+1]    = mem_wdata_r[63:32];
                mem_next[mem_addr_r*4+2]    = mem_wdata_r[95:64];
                mem_next[mem_addr_r*4+3]    = mem_wdata_r[127:96];
            end
            
            if( mem_read_r && ~mem_write_r ) begin
                mem_rdata_next = {mem[mem_addr_r*4+3],mem[mem_addr_r*4+2],mem[mem_addr_r*4+1],mem[mem_addr_r*4]};
            end
        end
    end

    always@( negedge clk ) begin
        state <= state_next;
        
        mem_ready <= mem_ready_next;
        mem_rdata  <= mem_rdata_next;
        
        for(i=0;i<MEM_NUM*4;i=i+1)
            mem[i] <= mem_next[i];
    end

    always@( negedge clk ) begin
        mem_read_r  <=  mem_read;
        mem_write_r <=  mem_write;
        mem_addr_r  <=  mem_addr;
        mem_wdata_r <=  mem_wdata;
    end

endmodule


  
  