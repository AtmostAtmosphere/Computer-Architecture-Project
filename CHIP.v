// Your code
`define ADD  4'b0000
`define SUB  4'b0001
`define SLL  4'b0010
`define SLT  4'b0011
`define SLTU 4'b0100
`define XOR  4'b0101
`define SRL  4'b0110
`define SRA  4'b0111
`define OR   4'b1000
`define AND  4'b1001
`define MUL  4'b1010
`define DIV  4'b1011
`define REM  4'b1100

`define R     7'b0110011
`define I     7'b0010011 
`define JALR  7'b1100111
`define LOAD  7'b0000011
`define STORE 7'b0100011 
`define SB    7'b1100011 
`define U     7'b0010111 
`define JAL   7'b1101111

// Branch
`define ISN_BRANCH 1'b0
`define IS_BRANCH 1'b1

// MemRead
`define ISN_MEMREAD 1'b0
`define IS_MEMREAD 1'b1

// MemWrite
`define ISN_MEMWRITE 1'b0
`define IS_MEMWRITE 1'b1

// RegWrite
`define ISN_REGWRITE 1'b0
`define IS_REGWRITE 1'b1

// MemtoReg
`define MEM2REG_PC_PLUS_4 2'b00
`define MEM2REG_ALU 2'b01
`define MEM2REG_MEM 2'b10
`define MEM2REG_PC_PLUS_IMM 2'b11

// ALUSrc
`define FROM_IMM 1'b1
`define FROM_RS2 1'b0

// PCCtrl
`define PCCTRL_PC_PLUS_IMM 2'b00
`define PCCTRL_RS1_PLUS_IMM 2'b01
`define PCCTRL_PC_PLUS_4 2'b10

module CHIP(clk,
            rst_n,
            // For mem_D
            mem_wen_D,
            mem_addr_D,
            mem_wdata_D,
            mem_rdata_D,
            // For mem_I
            mem_addr_I,
            mem_rdata_I
    );
    //==== I/O Declaration ========================
    input         clk, rst_n ;
    // For mem_D
    output        mem_wen_D  ;
    output [31:0] mem_addr_D ;
    output [31:0] mem_wdata_D;
    input  [31:0] mem_rdata_D;
    // For mem_I
    output [31:0] mem_addr_I ;
    input  [31:0] mem_rdata_I;

    //==== Reg/Wire Declaration ===================
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    reg   [31:0] PC_nxt      ;              //
    wire          regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    reg   [31:0] rd_data     ;              //
    //---------------------------------------//

    // Todo: other wire/reg

    wire    [24:0]  imm;
    wire    [6:0]   opcode;
    wire    [2:0]   funct3;
    wire    [6:0]   funct7;
    wire    [31:0] PC_plus_4;
    assign opcode = mem_rdata_I[6:0];
    assign rd = mem_rdata_I[11:7];
    assign funct3 = mem_rdata_I[14:12];
    assign rs1 = mem_rdata_I[19:15];
    assign rs2 = mem_rdata_I[24:20];
    assign funct7 = mem_rdata_I[31:25];
    assign imm = mem_rdata_I[31:7];
    assign PC_plus_4 = PC + 4;

    //==== Submodule Connection ===================
    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(regWrite),                      //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//

   
    //control signal
    wire is_branch, mem_read, mem_write, alu_src, reg_write;
    wire [1:0] mem_to_reg, pc_ctrl;

    assign regWrite = reg_write;

    wire [3:0] alu_ctrl;
    wire [31:0] extended_imm;
    wire alu_zero, alu_ready;
    wire [31:0] alu_result;
    reg [31:0] alu_input2;

    // Todo: other submodules
    //==== Combinational Part =====================
    Control control(
        .opcode(opcode),
        .is_branch(is_branch),
        .mem_to_reg(mem_to_reg),
        .pc_ctrl(pc_ctrl),
        .mem_read(mem_read),
        .mem_write(mem_write),
        .alu_src(alu_src),
        .reg_write(reg_write)
    );
    ALUctrl alu_control(
        .opcode(opcode),
        .funct3(funct3),
        .funct7(funct7),
        .alu_ctrl(alu_ctrl)
    );
    IMMGEN imm_gen(
        .instr(imm),
        .opcode(opcode),
        .imm(extended_imm)
    );


    // Todo: any combinational/sequential circuit
    //control the source of rs2
    always @(*) begin
        case(alu_src)
            `FROM_IMM: alu_input2 = extended_imm;
            `FROM_RS2: alu_input2 = rs2_data;
        endcase
    end

    ALU alu(
        .clk(clk),
        .rst_n(rst_n),
        .in1(rs1_data),
        .in2(alu_input2),
        .alu_ctrl(alu_ctrl),
        .out(alu_result),
        .out_zero(alu_zero),
        .alu_ready(alu_ready)
    );

    //control the assignment of rd_data
    always @(*) begin
        case(mem_to_reg)
            `MEM2REG_PC_PLUS_4: rd_data = PC_plus_4;
            `MEM2REG_ALU: rd_data = alu_result;
            `MEM2REG_MEM: rd_data = mem_rdata_D;
            `MEM2REG_PC_PLUS_IMM: rd_data = PC + extended_imm;
        endcase
    end

    //control the assignment PC
    always @(*) begin
        if(alu_ready)begin
            case(pc_ctrl)
                `PCCTRL_PC_PLUS_IMM: PC_nxt = (is_branch && alu_zero) ?  (PC + (extended_imm << 1)) : PC_plus_4;
                `PCCTRL_RS1_PLUS_IMM: PC_nxt = alu_result;
                `PCCTRL_PC_PLUS_4: PC_nxt = PC_plus_4;
                default : PC_nxt = PC ;
            endcase
        end
        else PC_nxt = PC ;
    end

    assign mem_wen_D = mem_write;
    assign mem_addr_D = alu_result;
    assign mem_wdata_D =  rs2_data;
    assign mem_addr_I = PC;

    //==== Sequential Part ========================
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00400000; // Do not modify this value!!!
        end
        else begin
            PC <= PC_nxt;
        end
    end
endmodule


module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);

    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth

    input clk, rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;

    output [BITS-1:0] q1, q2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign q1 = mem[a1];
    assign q2 = mem[a2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem[0] <= 0; // zero: hard-wired zero
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'h7fffeffc; // sp: stack pointer
                    32'd3: mem[i] <= 32'h10008000; // gp: global pointer
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end
    end
endmodule

module mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Todo: your HW2
    // Definition of ports
    input         clk, rst_n; //posedge triggered & asynchroonous negative edge reset
    input         valid; // valid input data when valid=1
    input  [1:0]  mode; // mode: 0: mulu, 1: divu, 2: shift, 3: avg
    output        ready; //ready output data when ready=1
    input  [31:0] in_A, in_B;
    output [63:0] out;

    // Definition of states
    parameter IDLE = 3'd0;
    parameter MUL  = 3'd1;
    parameter DIV  = 3'd2;
    parameter SHIFT = 3'd3;
    parameter AVG = 3'd4;
    parameter OUT  = 3'd5;

    // Todo: Wire and reg if needed
    reg  [ 2:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;
    reg ready_reg, div;
    // Todo: Instatiate any primitives if needed
    
    // Todo 5: Wire assignments
    assign out = shreg;
    assign ready = ready_reg;

    // Combinational always block
    // Todo 1: Next-state logic of state machine
    always @(*) begin
        case(state)
            IDLE: begin
                if (!valid) state_nxt = IDLE;
                else begin
                    if (mode == 2'd0) state_nxt = MUL;
                    else if (mode == 2'd1) state_nxt = DIV;
                    else if (mode == 2'd2) state_nxt = SHIFT;
                    else state_nxt = AVG;
                end
                ready_reg = 0;
            end
            MUL : begin
                state_nxt = (counter == 5'd31) ? OUT : MUL;
                ready_reg = 0;
            end
            DIV : begin
                state_nxt = (counter == 5'd31) ? OUT : DIV;
                ready_reg = 0;
            end
            SHIFT : begin
                state_nxt = OUT;
                ready_reg = 0;
            end
            
            AVG : begin
                state_nxt = OUT;
                ready_reg = 0;
            end
            
            OUT : begin
                state_nxt = IDLE;
                ready_reg = 1;
            end
            default : begin
                state_nxt = state;
                ready_reg = 0;
            end
            
        endcase
    end
    // Todo 2: Counter
    always @(*) begin
        case(state)
            MUL: counter_nxt = (counter < 31) ? (counter + 1) : 0; 
            DIV: counter_nxt = (counter < 31) ? (counter + 1) : 0;
            default: counter_nxt = 0;
        endcase
    end

    // ALU input
    always @(*) begin
        case(state)
            IDLE: alu_in_nxt = (valid) ? in_B : 0;
            OUT : alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end

    // Todo 3: ALU output
    always @(*) begin
        case(state)
            MUL: alu_out = (shreg[0]) ? {1'b0, alu_in} : 0;
            DIV: alu_out = (shreg[63:32] > alu_in) ? alu_in : 0;
            AVG: alu_out = (shreg[31:0] + alu_in) >> 1;
            default: alu_out = 0;
        endcase
    end
    
    // Todo 4: Shift register
    always @(*) begin
        case(state)
            IDLE: begin
                if(valid) shreg_nxt = (mode == 1) ? (in_A << 1) : in_A;
                else shreg_nxt = 0;
            end     
            MUL: shreg_nxt = {shreg[63:32] + alu_out, shreg[31:1]};
            DIV: begin 
                if (alu_out == 0) div = 0;
                else div = 1;
                shreg_nxt = shreg;
                shreg_nxt[63:32] = shreg[63:32] - alu_out;
                shreg_nxt = {shreg_nxt[62:0], div};
                if (counter == 31) 
                    shreg_nxt = {1'b0, shreg_nxt[63:33], shreg_nxt[31:0]};
                else
                    shreg_nxt = shreg_nxt;
            end
            SHIFT: shreg_nxt = shreg >> alu_in[2:0];
            AVG: shreg_nxt = {32'b0, alu_out[31:0]};
            default: shreg_nxt = 0;
        endcase
    end

    // Todo: Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            counter <= 0;
            alu_in <= 0;
            shreg <= 0;
        end
        else begin
            state <= state_nxt;
            counter <= counter_nxt;
            alu_in <= alu_in_nxt;
            shreg <= shreg_nxt;
        end
    end

endmodule

module IMMGEN(
    input   [24:0]  instr,
    input   [6:0]   opcode,
    output  [31:0]  imm
);
    reg [31:0] reg_imm;
    assign imm = reg_imm;

    always @(*) begin
        case(opcode)
            `R: reg_imm = 0;
            `I: reg_imm = {{20{instr[24]}}, instr[24:13]};
            `JALR: reg_imm = {{20{instr[24]}}, instr[24:13]};
            `LOAD: reg_imm = {{20{instr[24]}}, instr[24:13]};
            `STORE: reg_imm = {{20{instr[24]}}, instr[24:18], instr[4:0]};
            `SB: reg_imm = {{20{instr[24]}}, instr[24], instr[0], instr[23:18], instr[4:1]};
            `U: reg_imm = {instr[24:5] ,12'b0};
            `JAL: reg_imm = {{12{instr[24]}}, instr[24], instr[12:5], instr[13], instr[23:14]};
            default: reg_imm = 0;
        endcase
    end
endmodule

module Control(opcode, is_branch, mem_read, mem_to_reg, pc_ctrl, mem_write, alu_src, reg_write);
    input  [6:0] opcode;
    output reg is_branch, mem_read, mem_write, alu_src, reg_write;
    output reg [1:0] mem_to_reg, pc_ctrl;
    always @(*) begin 
        case(opcode)
            `R : begin
                is_branch   = `ISN_BRANCH;
                mem_to_reg  = `MEM2REG_ALU;
                pc_ctrl     = `PCCTRL_PC_PLUS_4;
                mem_read    = `ISN_MEMREAD;
                mem_write   = `ISN_MEMWRITE;
                alu_src     = `FROM_RS2;
                reg_write   = `IS_REGWRITE;
            end
            `I : begin
                is_branch   = `ISN_BRANCH;
                mem_to_reg  = `MEM2REG_ALU;
                pc_ctrl     = `PCCTRL_PC_PLUS_4;
                mem_read    = `ISN_MEMREAD;
                mem_write   = `ISN_MEMWRITE;
                alu_src     = `FROM_IMM;
                reg_write   = `IS_REGWRITE;
            end
            `JALR : begin
                is_branch   = `ISN_BRANCH;
                mem_to_reg  = `MEM2REG_PC_PLUS_4;
                pc_ctrl     = `PCCTRL_RS1_PLUS_IMM;
                mem_read    = `ISN_MEMREAD;
                mem_write   = `ISN_MEMWRITE;
                alu_src     = `FROM_IMM;
                reg_write   = `IS_REGWRITE;
            end
            `LOAD : begin
                is_branch   = `ISN_BRANCH;
                mem_to_reg  = `MEM2REG_MEM;
                pc_ctrl     = `PCCTRL_PC_PLUS_4;
                mem_read    = `IS_MEMREAD;
                mem_write   = `ISN_MEMWRITE;
                alu_src     = `FROM_IMM;
                reg_write   = `IS_REGWRITE;
            end
            `STORE : begin
                is_branch   = `ISN_BRANCH;
                mem_to_reg  = `MEM2REG_MEM;
                pc_ctrl     = `PCCTRL_PC_PLUS_4;
                mem_read    = `ISN_MEMREAD;
                mem_write   = `IS_MEMWRITE;
                alu_src     = `FROM_IMM;
                reg_write   = `ISN_REGWRITE;
            end
            `SB : begin
                is_branch   = `IS_BRANCH;
                mem_to_reg  = `MEM2REG_ALU;
                pc_ctrl     = `PCCTRL_PC_PLUS_IMM;
                mem_read    = `ISN_MEMREAD;
                mem_write   = `ISN_MEMWRITE;
                alu_src     = `FROM_RS2;
                reg_write   = `ISN_REGWRITE;
            end
            `U : begin
                is_branch   = `ISN_BRANCH;
                mem_to_reg  = `MEM2REG_PC_PLUS_IMM;
                pc_ctrl     = `PCCTRL_PC_PLUS_4;
                mem_read    = `ISN_MEMREAD;
                mem_write   = `ISN_MEMWRITE;
                alu_src     = `FROM_RS2;
                reg_write   = `IS_REGWRITE;
            end
            `JAL : begin
                is_branch   = `ISN_BRANCH;
                mem_to_reg  = `MEM2REG_PC_PLUS_4;
                pc_ctrl     = `PCCTRL_PC_PLUS_IMM;
                mem_read    = `ISN_MEMREAD;
                mem_write   = `ISN_MEMWRITE;
                alu_src     = `FROM_IMM;
                reg_write   = `IS_REGWRITE;
            end
            default : begin
                is_branch   = 0;
                mem_to_reg  = 0;
                pc_ctrl     = 0;
                mem_read    = 0;
                mem_write   = 0;
                alu_src     = 0;
                reg_write   = 0;
            end
        endcase
    end   
endmodule

module ALUctrl(opcode, funct3, funct7, alu_ctrl);
    input  [6:0]  opcode;
    input  [2:0]  funct3;
    input  [6:0]  funct7;
    output reg [3:0]  alu_ctrl;
    always @(*) begin 
        case(opcode)
            `R: begin
                if(funct7 == 7'b0000001) begin
                    if (funct3 == 3'b000) alu_ctrl = `MUL;
                    else if (funct3 == 3'b100) alu_ctrl = `DIV;
                    else alu_ctrl = `REM;
                end
                else begin
                    case(funct3)
                        3'b000: alu_ctrl = (funct7 == 0) ? `ADD : `SUB;
                        3'b001: alu_ctrl = `SLL;
                        3'b010: alu_ctrl = `SLT;
                        3'b011: alu_ctrl = `SLTU;
                        3'b100: alu_ctrl = `XOR;
                        3'b101: alu_ctrl = (funct7 == 0) ? `SRL : `SRA;
                        3'b110: alu_ctrl = `OR;
                        3'b111: alu_ctrl = `AND;
                    endcase
                end 
            end
            `I: begin
                case(funct3)
                    3'b000: alu_ctrl = `ADD;    // addi
                    3'b001: alu_ctrl = `SLL;    // slli
                    3'b010: alu_ctrl = `SLT;    // slti
                    3'b011: alu_ctrl = `SLTU;   // sltiu
                    3'b100: alu_ctrl = `XOR;    // xori
                    3'b101: alu_ctrl = (funct7 == 0) ? `SRL : `SRA; // srli, srai
                    3'b110: alu_ctrl = `OR;     // or
                    3'b111: alu_ctrl = `AND;    // andi
                endcase
            end
            `SB: alu_ctrl = `SUB; //beq
            default: alu_ctrl = `ADD;
        endcase
    end
endmodule


module ALU(clk, rst_n, in1, in2, alu_ctrl, out, out_zero, alu_ready);

    input [31:0] in1, in2;
    input [3:0] alu_ctrl;
    input clk, rst_n;
    output [31:0] out;
    output out_zero;
    output alu_ready;

    wire valid, ready;
    wire [1:0] mode;
    wire [63:0] muldiv_result;
    reg [31:0] alu_result;

    assign alu_ready = (alu_ctrl == `MUL || alu_ctrl == `DIV) ? ready : 1;
    assign out = alu_ready ? alu_result : 0;
    assign out_zero = (alu_ctrl == `SUB) ? (alu_result == 0) : 0;

    assign valid = (alu_ctrl == `MUL || alu_ctrl == `DIV);

    /*reg [1:0] reg_mode;
    if (alu_ctrl == `MUL) reg_mode = 1;
    else if (alu_ctrl == `DIV) reg_mode = 2;
    else reg_mode = 0; 
    assign mode = reg_mode;*/

    assign mode = (alu_ctrl == `MUL) ? 1 : 0;
    assign mode = (alu_ctrl == `DIV) ? 2 : 0;

    mulDiv mulDiv0(.clk(clk), .rst_n(rst_n), .valid(valid), .ready(ready), .mode(mode), .in_A(in1), .in_B(in2), .out(muldiv_out));
    
    always @(*) begin
        case(alu_ctrl)
            `ADD: alu_result  = in1 + in2; 
            `SUB: alu_result  = in1 - in2; 
            `XOR: alu_result  = in1 ^ in2; 
            `SLL: alu_result = in1 << in2;
            `SLTU: alu_result = in1 < in2;
            `XOR: alu_result = in1 ^ in2;
            `SRL: alu_result = in1 >>> in2;
            `SRA: alu_result = in1 >> in2;
            `OR: alu_result = in1 | in2;
            `AND: alu_result = in1 & in2;
            `MUL: alu_result = muldiv_result[31:0];
            `DIV: alu_result = muldiv_result[31:0];
            `SLT: begin
                if(in1[31] ^ in2[31]) alu_result = (in1[31] == 1);
                else alu_result = ((in1[31] == 0) ? (in1 < in2) : (in1 > in2));
            end
            default: alu_result  = 32'b0;
        endcase
    end
endmodule