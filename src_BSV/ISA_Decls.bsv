// Copyright (c) 2013-2016 Bluespec, Inc. All Rights Reserved

// ================================================================
// ISA defs for UC Berkeley RISC V
//
// References (from riscv.org):
//   "The RISC-V Instruction Set Manual
//    Volume I: User-Level ISA, Version 2.0, May 6, 2014"
//    Waterman, Lee, Patterson and Asanovic
//
//   "The RISC-V Instruction Set Manual
//    Volume II: Privileged Architecture, Version 1.7, May 9, 2015"
//    Waterman, Lee, Avizienis, Patterson and Asanovic
//
// ================================================================

package ISA_Decls;

// ================================================================
// BSV library imports

import DefaultValue :: *;
import Vector       :: *;
import BuildVector  :: *;

// ================================================================
// BSV project imports

// None

// ================================================================

typedef 3 NO_OF_PRIVMODES;

`ifdef RV32

typedef 32 XLEN;

`elsif RV64

typedef 64 XLEN;

`endif

typedef TMul #(2, XLEN)  XLEN_2;      // Double-width for multiplications

Integer xlen = valueOf (XLEN);

typedef enum { RV32, RV64 } RV_Version deriving (Eq, Bits);

RV_Version rv_version = ( (valueOf (XLEN) == 32) ? RV32 : RV64 );

// ----------------

typedef  8  Bits_per_Byte;

typedef  Bit #(XLEN)  Word;         // Raw (unsigned) register data
typedef  Int #(XLEN)  Word_S;       // Signed register data

typedef  Word         Addr;         // addresses/pointers

typedef TDiv #(XLEN, Bits_per_Byte)  Bytes_per_Word;
typedef TLog #(Bytes_per_Word)       Bits_per_Word_Byte_Index;

// ================================================================
// Instruction fields

typedef  Bit #(32)  Instr;
typedef  Bit #(7)   Opcode;
typedef  Bit #(5)   RegName;       // 32 registers, 0..31
typedef  32         NumRegs;
Integer  numRegs = valueOf (NumRegs);

function  Opcode     instr_opcode   (Instr x); return x [6:0]; endfunction

function  Bit #(3)   instr_funct3   (Instr x); return x [14:12]; endfunction
function  Bit #(5)   instr_funct5   (Instr x); return x [31:27]; endfunction
function  Bit#(7)    instr_funct7   (Instr x); return x [31:25]; endfunction
function  Bit #(10)  instr_funct10  (Instr x); return { x [31:25], x [14:12] }; endfunction

function  RegName    instr_rd       (Instr x); return x [11:7]; endfunction
function  RegName    instr_rs1      (Instr x); return x [19:15]; endfunction
function  RegName    instr_rs2      (Instr x); return x [24:20]; endfunction
function  RegName    instr_rs3      (Instr x); return x [31:27]; endfunction
function  CSR_Addr   instr_csr      (Instr x); return unpack(x [31:20]); endfunction

function  Bit #(12)  instr_I_imm12  (Instr x);
   return x [31:20];
endfunction

function  Bit #(12)  instr_S_imm12  (Instr x);
   return { x [31:25], x [11:7] };
endfunction

function  Bit #(13)  instr_SB_imm13 (Instr x);
   return { x [31], x [7], x [30:25], x [11:8], 1'b0 };
endfunction

function  Bit #(20)  instr_U_imm20  (Instr x);
   return x [31:12];
endfunction

function  Bit #(21)  instr_UJ_imm21 (Instr x);
   return { x [31], x [19:12], x [20], x [30:21], 1'b0 };
endfunction

// For FENCE decode
function  Bit #(4)   instr_pred (Instr x); return x [27:24]; endfunction
function  Bit #(4)   instr_succ (Instr x); return x [23:20]; endfunction

// For AMO decode
function  Bit #(2)   instr_aqrl (Instr x); return x [26:25]; endfunction

// ----------------
// Decoded instructions

typedef struct {
   Opcode    opcode;

   RegName   rd;
   RegName   rs1;
   RegName   rs2;
   RegName   rs3;
   CSR_Addr  csr;

   Bit #(3)  funct3;
   Bit #(5)  funct5;
   Bit #(7)  funct7;
   Bit #(10) funct10;

   Bit #(12) imm12_I;
   Bit #(12) imm12_S;
   Bit #(13) imm13_SB;
   Bit #(20) imm20_U;
   Bit #(21) imm21_UJ;

   Bit #(4)  pred;
   Bit #(4)  succ;

   Bit #(2)  aqrl;
   } Decoded_Instr
deriving (FShow, Bits);

function Decoded_Instr fv_decode (Instr instr);
   return Decoded_Instr {opcode:    instr_opcode (instr),

			 rd:        instr_rd       (instr),
			 rs1:       instr_rs1      (instr),
			 rs2:       instr_rs2      (instr),
			 rs3:       instr_rs3      (instr),
			 csr:       instr_csr      (instr),

			 funct3:    instr_funct3   (instr),
			 funct5:    instr_funct5   (instr),
			 funct7:    instr_funct7   (instr),
			 funct10:   instr_funct10  (instr),

			 imm12_I:   instr_I_imm12  (instr),
			 imm12_S:   instr_S_imm12  (instr),
			 imm13_SB:  instr_SB_imm13 (instr),
			 imm20_U:   instr_U_imm20  (instr),
			 imm21_UJ:  instr_UJ_imm21 (instr),

			 pred:      instr_pred     (instr),
			 succ:      instr_succ     (instr),

			 aqrl:      instr_aqrl     (instr)
			 };
endfunction

// ================================================================
// Symbolic register names

RegName x0  =  0;    RegName x1  =  1;    RegName x2  =  2;    RegName x3  =  3;
RegName x4  =  4;    RegName x5  =  5;    RegName x6  =  6;    RegName x7  =  7;
RegName x8  =  8;    RegName x9  =  9;    RegName x10 = 10;    RegName x11 = 11;
RegName x12 = 12;    RegName x13 = 13;    RegName x14 = 14;    RegName x15 = 15;
RegName x16 = 16;    RegName x17 = 17;    RegName x18 = 18;    RegName x19 = 19;
RegName x20 = 20;    RegName x21 = 21;    RegName x22 = 22;    RegName x23 = 23;
RegName x24 = 24;    RegName x25 = 25;    RegName x26 = 26;    RegName x27 = 27;
RegName x28 = 28;    RegName x29 = 29;    RegName x30 = 30;    RegName x31 = 31;

// Register names used in calling convention

RegName reg_ra = 1;

RegName reg_s0 = 2;  RegName reg_s1 = 3;  RegName reg_s2  = 4;  RegName reg_s3  = 5;
RegName reg_s4 = 6;  RegName reg_s5 = 7;  RegName reg_s6  = 8;  RegName reg_s7  = 9;
RegName reg_s8 = 10; RegName reg_s9 = 11; RegName reg_s10 = 12; RegName reg_s11 = 13;

RegName reg_sp = 14;
RegName reg_tp = 15;

RegName reg_v0 = 16;  RegName reg_v1 = 17;

RegName reg_a0 = 18;  RegName reg_a1 = 19; RegName reg_a2 = 20; RegName reg_a3 = 21;
RegName reg_a4 = 22;  RegName reg_a5 = 23; RegName reg_a6 = 24; RegName reg_a7 = 25;

RegName reg_t0 = 26;  RegName reg_t1 = 27; RegName reg_t2 = 28; RegName reg_t3 = 29;
RegName reg_t4 = 30;

RegName reg_gp = 31;

// ================================================================
// Data sizes for LOAD/STORE

typedef enum {BITS8,
	      BITS16,
	      BITS32,
	      BITS64    // Even in RV32, to allow for Double (floating point)
   } Mem_Data_Size
deriving (Eq, Bits, FShow);

// ================================================================
// LOAD/STORE instructions

Bit #(2) f3_SIZE_B = 2'b00;
Bit #(2) f3_SIZE_H = 2'b01;
Bit #(2) f3_SIZE_W = 2'b10;
Bit #(2) f3_SIZE_D = 2'b11;

// ----------------
// Load instructions

Opcode op_LOAD = 7'b00_000_11;

Bit #(3) f3_LB  = 3'b000;
Bit #(3) f3_LH  = 3'b001;
Bit #(3) f3_LW  = 3'b010;
Bit #(3) f3_LD  = 3'b011;
Bit #(3) f3_LBU = 3'b100;
Bit #(3) f3_LHU = 3'b101;
Bit #(3) f3_LWU = 3'b110;

// ----------------
// Store instructions

Opcode op_STORE = 7'b01_000_11;

Bit #(3) f3_SB  = 3'b000;
Bit #(3) f3_SH  = 3'b001;
Bit #(3) f3_SW  = 3'b010;
Bit #(3) f3_SD  = 3'b011;

// ================================================================
// Memory Model

Opcode op_MISC_MEM = 7'b00_011_11;

Bit #(3) f3_FENCE   = 3'b000;
Bit #(3) f3_FENCE_I = 3'b001;

// ================================================================
// Atomic Memory Operation Instructions

Opcode op_AMO = 7'b01_011_11;

// NOTE: bit [4] for aq, and [3] for rl, are here set to zero

Bit #(3)    f3_AMO_W     = 3'b010;
Bit #(3)    f3_AMO_D     = 3'b011;

Bit #(5)    f5_LR        = 5'b00010;
Bit #(5)    f5_SC        = 5'b00011;
Bit #(5)    f5_AMOADD    = 5'b00000;
Bit #(5)    f5_AMOSWAP   = 5'b00001;
Bit #(5)    f5_AMOXOR    = 5'b00100;
Bit #(5)    f5_AMOAND    = 5'b01100;
Bit #(5)    f5_AMOOR     = 5'b01000;
Bit #(5)    f5_AMOMIN    = 5'b10000;
Bit #(5)    f5_AMOMAX    = 5'b10100;
Bit #(5)    f5_AMOMINU   = 5'b11000;
Bit #(5)    f5_AMOMAXU   = 5'b11100;

Bit #(10) f10_LR_W       = 10'b00010_00_010;
Bit #(10) f10_SC_W       = 10'b00011_00_010;
Bit #(10) f10_AMOADD_W   = 10'b00000_00_010;
Bit #(10) f10_AMOSWAP_W  = 10'b00001_00_010;
Bit #(10) f10_AMOXOR_W   = 10'b00100_00_010;
Bit #(10) f10_AMOAND_W   = 10'b01100_00_010;
Bit #(10) f10_AMOOR_W    = 10'b01000_00_010;
Bit #(10) f10_AMOMIN_W   = 10'b10000_00_010;
Bit #(10) f10_AMOMAX_W   = 10'b10100_00_010;
Bit #(10) f10_AMOMINU_W  = 10'b11000_00_010;
Bit #(10) f10_AMOMAXU_W  = 10'b11100_00_010;

Bit #(10) f10_LR_D       = 10'b00010_00_011;
Bit #(10) f10_SC_D       = 10'b00011_00_011;
Bit #(10) f10_AMOADD_D   = 10'b00000_00_011;
Bit #(10) f10_AMOSWAP_D  = 10'b00001_00_011;
Bit #(10) f10_AMOXOR_D   = 10'b00100_00_011;
Bit #(10) f10_AMOAND_D   = 10'b01100_00_011;
Bit #(10) f10_AMOOR_D    = 10'b01000_00_011;
Bit #(10) f10_AMOMIN_D   = 10'b10000_00_011;
Bit #(10) f10_AMOMAX_D   = 10'b10100_00_011;
Bit #(10) f10_AMOMINU_D  = 10'b11000_00_011;
Bit #(10) f10_AMOMAXU_D  = 10'b11100_00_011;

// ================================================================
// Integer Register-Immediate Instructions

Opcode op_OP_IMM = 7'b00_100_11;

Bit #(3) f3_ADDI  = 3'b000;
Bit #(3) f3_SLLI  = 3'b001;
Bit #(3) f3_SLTI  = 3'b010;
Bit #(3) f3_SLTIU = 3'b011;
Bit #(3) f3_XORI  = 3'b100;
Bit #(3) f3_SRxI  = 3'b101; Bit #(3) f3_SRLI  = 3'b101; Bit #(3) f3_SRAI  = 3'b101;
Bit #(3) f3_ORI   = 3'b110;
Bit #(3) f3_ANDI  = 3'b111;

// ================================================================
// Integer Register-Immediate 32b Instructions for RV64

Opcode op_OP_IMM_32 = 7'b00_110_11;

Bit #(3) f3_ADDIW = 3'b000;
Bit #(3) f3_SLLIW = 3'b001;
Bit #(3) f3_SRxIW = 3'b101; Bit #(3) f3_SRLIW = 3'b101; Bit #(3) f3_SRAIW = 3'b101;

// ================================================================
// Integer Register-Register Instructions

Opcode op_OP = 7'b01_100_11;

Bit #(10) f10_ADD    = 10'b000_0000_000;
Bit #(10) f10_SUB    = 10'b010_0000_000;
Bit #(10) f10_SLL    = 10'b000_0000_001;
Bit #(10) f10_SLT    = 10'b000_0000_010;
Bit #(10) f10_SLTU   = 10'b000_0000_011;
Bit #(10) f10_XOR    = 10'b000_0000_100;
Bit #(10) f10_SRL    = 10'b000_0000_101;
Bit #(10) f10_SRA    = 10'b010_0000_101;
Bit #(10) f10_OR     = 10'b000_0000_110;
Bit #(10) f10_AND    = 10'b000_0000_111;

Bit #(7) f7_MUL_DIV_REM = 7'b000_0001;

function Bool f7_is_OP_MUL_DIV_REM (Bit #(7) f7);
   return (f7 == f7_MUL_DIV_REM);
endfunction

Bit #(3) f3_MUL    = 3'b000;
Bit #(3) f3_MULH   = 3'b001;
Bit #(3) f3_MULHSU = 3'b010;
Bit #(3) f3_MULHU  = 3'b011;
Bit #(3) f3_DIV    = 3'b100;
Bit #(3) f3_DIVU   = 3'b101;
Bit #(3) f3_REM    = 3'b110;
Bit #(3) f3_REMU   = 3'b111;

// ================================================================
// Integer Register-Register 32b Instructions for RV64

Opcode op_OP_32 = 7'b01_110_11;

Bit #(10) f10_ADDW   = 10'b000_0000_000;
Bit #(10) f10_SUBW   = 10'b010_0000_000;
Bit #(10) f10_SLLW   = 10'b000_0000_001;
Bit #(10) f10_SRLW   = 10'b000_0000_101;
Bit #(10) f10_SRAW   = 10'b010_0000_101;

Bit #(10) f10_MULW   = 10'b000_0001_000;
Bit #(10) f10_DIVW   = 10'b000_0001_100;
Bit #(10) f10_DIVUW  = 10'b000_0001_101;
Bit #(10) f10_REMW   = 10'b000_0001_110;
Bit #(10) f10_REMUW  = 10'b000_0001_111;

function Bool is_OP_32_MUL_DIV_REM (Bit #(10) f10);
   return (   (f10 == f10_MULW)
	   || (f10 == f10_DIVW)
	   || (f10 == f10_DIVUW)
	   || (f10 == f10_REMW)
	   || (f10 == f10_REMUW));
endfunction

// ================================================================
// LUI, AUIPC

Opcode op_LUI   = 7'b01_101_11;
Opcode op_AUIPC = 7'b00_101_11;

// ================================================================
// Control transfer

Opcode  op_BRANCH = 7'b11_000_11;

Bit #(3) f3_BEQ   = 3'b000;
Bit #(3) f3_BNE   = 3'b001;
Bit #(3) f3_BLT   = 3'b100;
Bit #(3) f3_BGE   = 3'b101;
Bit #(3) f3_BLTU  = 3'b110;
Bit #(3) f3_BGEU  = 3'b111;

Opcode op_JAL  = 7'b11_011_11;

Opcode op_JALR = 7'b11_001_11;

// ================================================================
// System Instructions
Opcode op_SYSTEM = 7'b11_100_11;

Bit #(12) f12_ECALL     = 12'b_0000_0000_0000;
Bit #(12) f12_EBREAK    = 12'b_0000_0000_0001;
Bit #(12) f12_ERET      = 12'b_0001_0000_0000;

Instr break_instr = { f12_EBREAK, 5'b00000, 3'b000, 5'b00000, op_SYSTEM };

// sub-opcodes: (in funct3 field)
Bit #(3)   f3_PRIV       = 3'b000;
Bit #(3)   f3_CSRRW      = 3'b001;
Bit #(3)   f3_CSRRS      = 3'b010;
Bit #(3)   f3_CSRRC      = 3'b011;
Bit #(3)   f3_CSRRWI     = 3'b101;
Bit #(3)   f3_CSRRSI     = 3'b110;
Bit #(3)   f3_CSRRCI     = 3'b111;

// Trap redirection (in {f5,rs2} a.k.a. I_imm12, call it f12
Bit #(12) f12_MRTS      = 12'b0011_0000_0101;
Bit #(12) f12_MRTH      = 12'b0011_0000_0110;
Bit #(12) f12_HRTS      = 12'b0011_0000_0101;

// Wait for Interrupt
Bit #(12) f12_WFI       = 12'b0001_0000_0010;

// SFENCE.VM
Bit #(12) f12_SFENCE_VM = 12'b0001_0000_0001;

function Bool is_SYSTEM_PRIV (Instr instr);
   return (   (instr_opcode (instr) == op_SYSTEM)
	   && (instr_funct3 (instr) == f3_PRIV));
endfunction

// ================================================================
// Privilege levels

typedef Bit #(2) Priv_Mode;

Priv_Mode  u_Priv_Mode = 2'b00;
Priv_Mode  s_Priv_Mode = 2'b01;
Priv_Mode  h_Priv_Mode = 2'b10;
Priv_Mode  m_Priv_Mode = 2'b11;

function Action show_Priv_Mode (Priv_Mode priv);
   action
      case (priv)
	 u_Priv_Mode: $write ("U");
	 s_Priv_Mode: $write ("S");
	 h_Priv_Mode: $write ("H");
	 m_Priv_Mode: $write ("M");
      endcase
   endaction
endfunction

// ================================================================
// Control/Status register addresses

typedef Bit #(12) CSR_Addr;

// ----------------
// User-level CSRs

CSR_Addr   csr_FFLAGS    = 12'h001;    // Floating-point accrued exceptions
CSR_Addr   csr_FRM       = 12'h002;    // Floating-point Dynamic Rounding Mode
CSR_Addr   csr_FCSR      = 12'h003;    // Floating-point Control and Status Register

CSR_Addr   csr_CYCLE     = 12'hc00;    // Cycle counter for RDCYCLE
CSR_Addr   csr_TIME      = 12'hc01;    // Timer for RDTIME
CSR_Addr   csr_INSTRET   = 12'hc02;    // Instructions retired, for RDINSTRET

CSR_Addr   csr_CYCLEH    = 12'hc80;    // Upper 32 bits of CYCLE (RV32I only)
CSR_Addr   csr_TIMEH     = 12'hc81;    // Upper 32 bits of TIME (RV32I only)
CSR_Addr   csr_INSTRETH  = 12'hc82;    // Upper 32 bits of INSTRET (RV32I only)

// ----------------
// Supervisor-level CSRs

CSR_Addr   csr_SSTATUS    = 12'h100;    // status
CSR_Addr   csr_STVEC      = 12'h101;    // trap handler base address
CSR_Addr   csr_SIE        = 12'h104;    // interrupt-enable
CSR_Addr   csr_STIMECMP   = 12'h121;    // wall-clock timer compare value

CSR_Addr   csr_STIME      = 12'hD01;    // wall-clock timer compare value
CSR_Addr   csr_STIMEH     = 12'hD81;    // upper 32b of STIME (RV32I only)

CSR_Addr   csr_SSCRATCH   = 12'h140;    // scratch reg for supervisor trap handlers
CSR_Addr   csr_SEPC       = 12'h141;    // exception program counter
CSR_Addr   csr_SCAUSE     = 12'hD42;    // trap cause
CSR_Addr   csr_SBADADDR   = 12'hD43;    // bad address
CSR_Addr   csr_SIP        = 12'h144;    // interrupt pending

CSR_Addr   csr_SPTBR      = 12'h180;    // Page-table base register
CSR_Addr   csr_SASID      = 12'h181;    // Address-space ID

CSR_Addr   csr_CYCLEW     = 12'h900;    // CYCLE; writeable
CSR_Addr   csr_TIMEW      = 12'h901;    // TIME, writeable
CSR_Addr   csr_INSTRETW   = 12'h902;    // INSTRET, writeable

CSR_Addr   csr_CYCLEHW    = 12'h980;    // CYCLEH, writeable
CSR_Addr   csr_TIMEHW     = 12'h981;    // TIMEH, writeable
CSR_Addr   csr_INSTRETHW  = 12'h982;    // INSTRETH, writeable

// ----------------
// Hypervisor-level CSRs

CSR_Addr   csr_HSTATUS    = 12'h200;    // status
CSR_Addr   csr_HTVEC      = 12'h201;    // trap handler base address
CSR_Addr   csr_HTDELEG    = 12'h202;    // trap delegation
CSR_Addr   csr_HIE        = 12'h204;    // interrupt-enable
CSR_Addr   csr_HTIMECMP   = 12'h221;    // wall-clock timer compare value

CSR_Addr   csr_HTIME      = 12'hE01;    // wall-clock timer compare value
CSR_Addr   csr_HTIMEH     = 12'hE81;    // upper 32b of HTIME (RV32I only)

CSR_Addr   csr_HSCRATCH   = 12'h240;    // scratch reg for hypervisor trap handlers
CSR_Addr   csr_HEPC       = 12'h241;    // exception program counter
CSR_Addr   csr_HCAUSE     = 12'h242;    // trap cause
CSR_Addr   csr_HBADADDR   = 12'h243;    // bad address

CSR_Addr   csr_STIMEW     = 12'hA01;    // STIME writeable
CSR_Addr   csr_STIMEHW    = 12'hA81;    // STIMEH, writeable

// ----------------
// Machine-level CSRs

CSR_Addr   csr_MCPUID     = 12'hF00;    // CPU description
CSR_Addr   csr_MIMPID     = 12'hF01;    // Vendor ID and version number
CSR_Addr   csr_MHARTID    = 12'hF10;    // Hardware thread ID

CSR_Addr   csr_MSTATUS    = 12'h300;    // status
CSR_Addr   csr_MTVEC      = 12'h301;    // trap handler base address
CSR_Addr   csr_MTDELEG    = 12'h302;    // trap delegation
CSR_Addr   csr_MIE        = 12'h304;    // interrupt-enable
CSR_Addr   csr_MTIMECMP   = 12'h321;    // wall-clock timer compare value

CSR_Addr   csr_MTIME      = 12'h701;    // wall-clock timer compare value
CSR_Addr   csr_MTIMEH     = 12'h741;    // upper 32b of HTIME (RV32I only)

CSR_Addr   csr_MSCRATCH   = 12'h340;    // scratch reg for machine trap handlers
CSR_Addr   csr_MEPC       = 12'h341;    // exception program counter
CSR_Addr   csr_MCAUSE     = 12'h342;    // trap cause
CSR_Addr   csr_MBADADDR   = 12'h343;    // bad address
CSR_Addr   csr_MIP        = 12'h344;    // interrupt pending

CSR_Addr   csr_MBASE      = 12'h380;    // base
CSR_Addr   csr_MBOUND     = 12'h381;    // bound
CSR_Addr   csr_MIBASE     = 12'h382;    // instruction base
CSR_Addr   csr_MIBOUND    = 12'h383;    // instruction bound
CSR_Addr   csr_MDBASE     = 12'h384;    // data base
CSR_Addr   csr_MDBOUND    = 12'h385;    // data bound

CSR_Addr   csr_HTIMEW     = 12'hB01;    // HTIME writeable
CSR_Addr   csr_HTIMEHW    = 12'hB81;    // HTIMEH, writeable

CSR_Addr   csr_MTOHOST    = 12'h780;    // Test output register
CSR_Addr   csr_MFROMHOST  = 12'h781;    // Test input register

// ----------------
// Bit-fields of the CSR_MSTATUS register

Integer mstatus_SD_index   = xlen-1;
Integer mstatus_VM_hi      = 21;        Integer mstatus_VM_lo      = 17;
Integer mstatus_MPRV_index = 16;
Integer mstatus_XS_hi      = 15;        Integer mstatus_XS_lo   = 14;
Integer mstatus_FS_hi      = 13;        Integer mstatus_FS_lo   = 12;
Integer mstatus_PRV3_hi    = 11;        Integer mstatus_PRV3_lo = 10;
Integer mstatus_IE3_index  =  9;
Integer mstatus_PRV2_hi    =  8;        Integer mstatus_PRV2_lo = 7;
Integer mstatus_IE2_index  =  6;
Integer mstatus_PRV1_hi    =  5;        Integer mstatus_PRV1_lo = 4;
Integer mstatus_IE1_index  =  3;
Integer mstatus_PRV_hi     =  2;        Integer mstatus_PRV_lo  = 1;
Integer mstatus_IE_index   =  0;

// ----------------
// Help functions to manipulate mstatus

function  Vector #(n, PrvStat)  mstatus_priv_vec (Word mstatus)
   provisos (Add #(n, _j, 4));
   Vector #(4, PrvStat) priv_vec = unpack (mstatus [mstatus_PRV3_hi: mstatus_IE_index]);
   return take (priv_vec);
endfunction

function  Word  upd_mstatus_priv_vec  (Word mstatus, Vector #(n, PrvStat) priv_vec)
   provisos (Add #(n, _j, 4));
   Vector #(4, PrvStat) full_priv_vec = append (priv_vec, replicate (unused_PrvStat));
   return { mstatus [xlen-1:mstatus_FS_lo], pack (full_priv_vec) };
endfunction

function  Priv_Mode  mstatus_PRV (Word mstatus);
   Vector #(NO_OF_PRIVMODES, PrvStat) priv_vec = mstatus_priv_vec (mstatus);
   return priv_vec[0].prv;
endfunction

function  Word  upd_mstatus_PRV (Word mstatus, Priv_Mode prv);
   Vector #(NO_OF_PRIVMODES, PrvStat) priv_vec = mstatus_priv_vec (mstatus);
   priv_vec[0].prv = prv;
   return upd_mstatus_priv_vec (mstatus, priv_vec);
endfunction

function  Word  push_mstatus_priv_vec  (Word mstatus, Priv_Mode prv);
   Vector #(NO_OF_PRIVMODES, PrvStat)  old_priv_vec = mstatus_priv_vec (mstatus);
   let new_priv_vec = shiftInAt0 (old_priv_vec, PrvStat { prv: prv, ie: False });
   return upd_mstatus_priv_vec (mstatus, new_priv_vec);
endfunction

function  Word  pop_mstatus_priv_vec  (Word mstatus);
   Vector #(NO_OF_PRIVMODES, PrvStat)  old_priv_vec = mstatus_priv_vec (mstatus);
   let new_priv_vec = shiftInAtN (old_priv_vec, defaultValue);
   return upd_mstatus_priv_vec (mstatus, new_priv_vec);
endfunction

function  Priv_Mode  mstatus_PRV1 (Word mstatus);
   Vector #(NO_OF_PRIVMODES, PrvStat) priv_vec = mstatus_priv_vec (mstatus);
   return priv_vec[1].prv;
endfunction

function  Bool  mstatus_MPRV (Word mstatus);
   return mstatus[mstatus_MPRV_index] == 1;
endfunction

typedef struct {
   Priv_Mode prv;
   Bool      ie;
		} PrvStat deriving (Bits, Eq);

// This is the value for all stack entries below top-of-stack, at RESET
PrvStat unused_PrvStat = PrvStat { prv: u_Priv_Mode, ie: False };

// This is the value inserted at the bottom of the stack by ERET
instance DefaultValue#(PrvStat);
   defaultValue = PrvStat { prv: u_Priv_Mode, ie: True };  // thus spec 1.7
endinstance

// ----------------
// Extension Context Status (mstatus.fs and mstatus.xs)

Bit #(2) ecs_off      = 2'h0;
Bit #(2) ecs_initial  = 2'h1;
Bit #(2) ecs_clean    = 2'h2;
Bit #(2) ecs_dirty    = 2'h3;

// ----------------
// Standard mtvec and reset vector values
// MTVEC reg can be hardwired to hi or lo value
// reset value should correspond.

Word mtvec_std_hi = (~ 'h01FF);    // = 0xF...FFE00
Word mtvec_std_lo = 'h0100;

`ifdef MTVEC_STD_HI
   Word mtvec_reset_value = mtvec_std_hi;
`else
   Word mtvec_reset_value = mtvec_std_lo;
`endif

Word pc_reset_value    = (mtvec_reset_value + 'h100);    // 'h0200 or 'hFFFF....F00

// ----------------
// MTDELEG/HTDELEG fields

Integer tdeleg_MTIP_index = 23;
Integer tdeleg_HTIP_index = 22;
Integer tdeleg_STIP_index = 21;

Integer tdeleg_MSIP_index = 19;
Integer tdeleg_HSIP_index = 18;
Integer tdeleg_SSIP_index = 17;

Integer tdeleg_traps_hi = 15;
Integer tdeleg_traps_lo = 0;

// ----------------
// MIP and MIE fields (interrupt pending, interrupt enable)

// External interrupt
Integer mxi_index = 19;
Integer hxi_index = 18;
Integer sxi_index = 17;

// Timer interrupts
Integer mti_index = 7;
Integer hti_index = 6;
Integer sti_index = 5;    // Also in SIP reg

// Software interrupts
Integer msi_index = 3;
Integer hsi_index = 2;
Integer ssi_index = 1;    // Also in SIE reg

// ----------------
// MCAUSE (reason for exception)

Integer mcause_interrupt_index  = xlen - 1;
Integer mcause_zero_index       = 4;
Integer mcause_exc_code_hi      = 3;    Integer mcause_exc_code_lo   = 0;

typedef Bit #(4) Exc_Code;

// When Interrupt = 0 (trap)

Exc_Code exc_code_MISALIGNED_FETCH     = 4'h0;
Exc_Code exc_code_FAULT_FETCH          = 4'h1;
Exc_Code exc_code_ILLEGAL_INSTRUCTION  = 4'h2;
Exc_Code exc_code_BREAKPOINT           = 4'h3;

Exc_Code exc_code_MISALIGNED_LOAD      = 4'h4;
Exc_Code exc_code_FAULT_LOAD           = 4'h5;

Exc_Code exc_code_MISALIGNED_STORE_AMO = 4'h6;
Exc_Code exc_code_FAULT_STORE_AMO      = 4'h7;

Exc_Code exc_code_ECALL_FROM_U         = 4'h8;
Exc_Code exc_code_ECALL_FROM_S         = 4'h9;
Exc_Code exc_code_ECALL_FROM_H         = 4'hA;
Exc_Code exc_code_ECALL_FROM_M         = 4'hB;

// When Interrupt = 1 (interrupt)

Exc_Code exc_code_SW_INTERRUPT         = 4'h0;
Exc_Code exc_code_TIMER_INTERRUPT      = 4'h1;

Maybe #(Exc_Code) m_trap_none             = tagged Invalid;
Maybe #(Exc_Code) m_trap_illegal_instr    = tagged Valid exc_code_ILLEGAL_INSTRUCTION;

function Action show_Trap_Exc_Code (Exc_Code exc);
   action
      case (exc)
	 exc_code_MISALIGNED_FETCH:     $write ("MISALIGNED_FETCH");
	 exc_code_FAULT_FETCH:          $write ("FAULT_FETCH");
	 exc_code_ILLEGAL_INSTRUCTION:  $write ("ILLEGAL_INSTRUCTION");
	 exc_code_BREAKPOINT:           $write ("BREAKPOINT");

	 exc_code_MISALIGNED_LOAD:      $write ("MISALIGNED_LOAD");
	 exc_code_FAULT_LOAD:           $write ("FAULT_LOAD");

	 exc_code_MISALIGNED_STORE_AMO: $write ("MISALIGNED_STORE_AMO");
	 exc_code_FAULT_STORE_AMO:      $write ("FAULT_STORE_AMO");

	 exc_code_ECALL_FROM_U:         $write ("ECALL_FROM_U");
	 exc_code_ECALL_FROM_S:         $write ("ECALL_FROM_S");
	 exc_code_ECALL_FROM_H:         $write ("ECALL_FROM_H");
	 exc_code_ECALL_FROM_M:         $write ("ECALL_FROM_M");
	 default:                       $write ("unknown Exc_Code 0x%0h", exc);
      endcase
   endaction
endfunction

// ----------------
// Bit-fields of the CSR_SSTATUS register

function bit sstatus_sd   (Word sstatus_val); return sstatus_val [xlen-1]; endfunction
function Bit #(TSub #(XLEN,18)) sstatus_mbz_17 (Word sstatus_val);
   return sstatus_val [xlen-2:17];
endfunction
function bit      sstatus_mprv  (Word sstatus_val); return sstatus_val [16]; endfunction
function Bit #(2) sstatus_xs    (Word sstatus_val); return sstatus_val [15:14]; endfunction
function Bit #(2) sstatus_fs    (Word sstatus_val); return sstatus_val [13:12]; endfunction
function Bit #(7) sstatus_mbz_5 (Word sstatus_val); return sstatus_val [11:5]; endfunction
function bit      sstatus_ps    (Word sstatus_val); return sstatus_val [4]; endfunction
function bit      sstatus_pie   (Word sstatus_val); return sstatus_val [3]; endfunction
function Bit #(2) sstatus_mbz_1 (Word sstatus_val); return sstatus_val [2:1]; endfunction
function bit      sstatus_ie    (Word sstatus_val); return sstatus_val [0]; endfunction

// ----------------
// SCAUSE (reason for exception)

function bit scause_interrupt (Word scause_val); return scause_val [xlen-1]; endfunction
function Bit #(TSub #(XLEN,5)) scause_mbz_5 (Word scause_val); return scause_val [xlen-2:4]; endfunction
function Bit #(4) scause_exception_code (Word scause_val); return scause_val [3:0]; endfunction

// ----------------
// SPTBR (supervisor page table)

function Bit #(4)  sptbr_base  (Word sptbr_val); return sptbr_val [xlen-1:11]; endfunction
function Bit #(12) sptbr_mbz_0 (Word sptbr_val); return sptbr_val [11:0]; endfunction

// ================================================================
// Virtualization schemes (mstatus.vm)

typedef Bit #(5) VM_Scheme;

VM_Scheme vm_mbare  = 5'h0;
VM_Scheme vm_mbb    = 5'h1;
VM_Scheme vm_mbbid  = 5'h2;

VM_Scheme vm_sv32   = 5'h8;
VM_Scheme vm_sv39   = 5'h9;
VM_Scheme vm_sv48   = 5'ha;
VM_Scheme vm_sv57   = 5'hb;
VM_Scheme vm_sv64   = 5'hc;

function  VM_Scheme  mstatus_VM (Word mstatus);
   return mstatus [mstatus_VM_hi: mstatus_VM_lo];
endfunction

function Action show_VM_Scheme (String pre, VM_Scheme vm, String post);
   action
      $write ("%s", pre);
      case (vm)
	 vm_mbare: $write ("MBare");
	 vm_mbb:   $write ("Mbb");
	 vm_mbbid: $write ("Mbbid");

	 vm_sv32:  $write ("Sv32");
	 vm_sv39:  $write ("Sv39");
	 vm_sv48:  $write ("Sv48");
	 vm_sv57:  $write ("Sv57");
	 vm_sv64:  $write ("Sv64");
	 default:  $write ("unknown VM_Scheme 0x%0h", vm);
      endcase
      $write ("%s", post);
   endaction
endfunction

// ----------------------------------------------------------------
// Virtual and Physical addresses, page numbers, offsets
// Page table (PT) fields and entries (PTEs)
// For Sv32 and Sv39

// ----------------
`ifdef RV32

// Virtual addrs
typedef   32  VA_sz;
typedef   20  VPN_sz;
typedef   10  VPN_J_sz;
typedef   12  Offset_sz;

// Physical addrs
typedef   34  PA_sz;
typedef   22  PPN_sz;
typedef   12  PPN_1_sz;
typedef   10  PPN_0_sz;

// PTNodes
typedef 1024  PTNode_sz;    // # of PTEs in a PTNode

// ----------------
`elsif RV64

// Virtual addrs
typedef   39  VA_sz;
typedef   27  VPN_sz;
typedef    9  VPN_J_sz;
typedef   12  Offset_sz;

// Physical addrs
typedef   50  PA_sz;
typedef   38  PPN_sz;
typedef   20  PPN_2_sz;
typedef    9  PPN_1_sz;
typedef    9  PPN_0_sz;

// PTNodes
typedef  512  PTNode_sz;    // # of PTEs in a PTNode

`endif

// ----------------
// Derived types and values

Integer  va_sz     = valueOf (VA_sz);        typedef Bit #(VA_sz)      VA;
Integer  vpn_sz    = valueOf (VPN_sz);       typedef Bit #(VPN_sz)     VPN;
Integer  vpn_j_sz  = valueOf (VPN_J_sz);     typedef Bit #(VPN_J_sz)   VPN_J;
Integer  offset_sz = valueOf (Offset_sz);    typedef Bit #(Offset_sz)  Offset;

function  Offset  fn_offset_in_page (Bit #(n) va)
   provisos (Add #(Offset_sz, something, n));
   return va [offset_sz - 1: 0];
endfunction

function  VPN  fn_va_vpn (VA va);
   return va [vpn_sz + offset_sz - 1: offset_sz];
endfunction

// Physical addrs
Integer  pa_sz    = valueOf (PA_sz);     typedef Bit #(PA_sz)     PA;
Integer  ppn_sz   = valueOf (PPN_sz);    typedef Bit #(PPN_sz)    PPN;
`ifdef RV64
Integer  ppn_2_sz = valueOf (PPN_2_sz);  typedef Bit #(PPN_2_sz)  PPN_2;
`endif
Integer  ppn_1_sz = valueOf (PPN_1_sz);  typedef Bit #(PPN_1_sz)  PPN_1;
Integer  ppn_0_sz = valueOf (PPN_0_sz);  typedef Bit #(PPN_0_sz)  PPN_0;

function PA fn_Word_to_PA (Word v);
`ifdef RV32
   return extend (v);
`elsif RV64
   return truncate (v);
`endif
endfunction

function  PPN  fn_pa_ppn (PA pa);
   return pa [ppn_sz + offset_sz - 1: offset_sz];
endfunction

// ----------------
// PTNodes

Integer  ptnode_sz = valueOf (PTNode_sz);    // # of PTEs in a PTNode
typedef  TLog #(PTNode_sz)       PTNode_Index_sz;
typedef  Bit #(PTNode_Index_sz)  PTNode_Index;
Integer  ptnode_index_sz = valueOf (PTNode_Index_sz);

// ----------------
// PTEs (Page Table Entries)

typedef Word PTE;

Integer  pte_PPN_offset  = 10;

Integer  pte_D_offset    = 6;
Integer  pte_R_offset    = 5;
Integer  pte_Type_offset = 1;
Integer  pte_V_offset    = 0;

typedef  4  PTE_Type_sz;                  Integer  pte_Type_sz     = 4;
typedef  Bit #(PTE_Type_sz) PTE_Type;


PTE_Type  pte_Type_ptr                    = 0;
PTE_Type  pte_Type_ptr_global             = 1;

PTE_Type  pte_Type_s_r___u_r_x            = 2;
PTE_Type  pte_Type_s_rw__u_rwx            = 3;
PTE_Type  pte_Type_s_r___u_r__            = 4;
PTE_Type  pte_Type_s_rw__u_rw_            = 5;
PTE_Type  pte_Type_s_r_x_u_r_x            = 6;
PTE_Type  pte_Type_s_rwx_u_rwx            = 7;

PTE_Type  pte_Type_s_r___u____            = 8;
PTE_Type  pte_Type_s_rw__u____            = 9;
PTE_Type  pte_Type_s_r_x_u____           = 10;
PTE_Type  pte_Type_s_rwx_u____           = 11;

PTE_Type  pte_Type_s_r___u_____global    = 12;
PTE_Type  pte_Type_s_rw__u_____global    = 13;
PTE_Type  pte_Type_s_r_x_u_____global    = 14;
PTE_Type  pte_Type_s_rwx_u_____global    = 15;


function PPN fn_pte_PPN (PTE pte);
   return pte [ppn_sz + pte_PPN_offset - 1 : pte_PPN_offset];
endfunction

function PTE_Type fn_pte_Type (PTE pte);
   return pte [pte_Type_sz + pte_Type_offset - 1 : pte_Type_offset];
endfunction

function Bit #(1) fn_pte_V (PTE pte);
   return pte [pte_V_offset];
endfunction

function Bit #(1) fn_pte_R (PTE pte);
   return pte [pte_R_offset];
endfunction

function Bit #(1) fn_pte_D (PTE pte);
   return pte [pte_D_offset];
endfunction

// ----------------
// PTE control bits for access rights

typedef struct {
   Bool  g;
   Bool  p;

   // Supervisor mode permissions (read, write, exec)
   Bool sr;
   Bool sw;
   Bool sx;
   // User mode permissions (read, write, exec)
   Bool ur;
   Bool uw;
   Bool ux;
   } PTEbits deriving (Bits, FShow);

// Ref. Table 4.2 in PrivArch Spec v1.7
Vector#(16, PTEbits) rights =
   vec (PTEbits{g:False, p: True,   sr:False, sw:False, sx:False,  ur:False, uw:False, ux:False}, // 0
        PTEbits{g:True,  p: True,   sr:False, sw:False, sx:False,  ur:False, uw:False, ux:False}, // 1

	PTEbits{g:False, p: False,  sr:True,  sw:False, sx:False,  ur:True,  uw:False, ux:True }, // 2
	PTEbits{g:False, p: False,  sr:True,  sw:True,  sx:False,  ur:True,  uw:True,  ux:True }, // 3
	PTEbits{g:False, p: False,  sr:True,  sw:False, sx:False,  ur:True,  uw:False, ux:False}, // 4
	PTEbits{g:False, p: False,  sr:True,  sw:True,  sx:False,  ur:True,  uw:True,  ux:False}, // 5
	PTEbits{g:False, p: False,  sr:True,  sw:False, sx:True,   ur:True,  uw:False, ux:True }, // 6
	PTEbits{g:False, p: False,  sr:True,  sw:True,  sx:True,   ur:True,  uw:True,  ux:True }, // 7

	PTEbits{g:False, p: False,  sr:True,  sw:False, sx:False,  ur:False, uw:False, ux:False}, // 8
	PTEbits{g:False, p: False,  sr:True,  sw:True,  sx:False,  ur:False, uw:False, ux:False}, // 9
	PTEbits{g:False, p: False,  sr:True,  sw:False, sx:True,   ur:False, uw:False, ux:False}, // 10
	PTEbits{g:False, p: False,  sr:True,  sw:True,  sx:True,   ur:False, uw:False, ux:False}, // 11

	PTEbits{g:True,  p: False,  sr:True,  sw:False, sx:False,  ur:False, uw:False, ux:False}, // 12
	PTEbits{g:True,  p: False,  sr:True,  sw:True,  sx:False,  ur:False, uw:False, ux:False}, // 13
	PTEbits{g:True,  p: False,  sr:True,  sw:False, sx:True,   ur:False, uw:False, ux:False}, // 14
	PTEbits{g:True,  p: False,  sr:True,  sw:True,  sx:True,   ur:False, uw:False, ux:False});// 15

// ----------------
// Check if PTE permits access COMMAND (READ/WRITE) in privilege level PRIV (User/Supervisor...)

function Bool fn_vm_access_permitted (Bool       dmem_not_imem,
				      Bool       read_not_write,
				      Priv_Mode  priv,
				      PTE        pte);
   PTEbits  bs  = rights [fn_pte_Type (pte)];

   return case (tuple2 (dmem_not_imem, read_not_write)) matches
	     { True, True  } : ((priv == u_Priv_Mode) ? bs.ur : bs.sr);
	     { True, False } : ((priv == u_Priv_Mode) ? bs.uw : bs.sw);
	     { False, True } : ((priv == u_Priv_Mode) ? bs.ux : bs.sx);
	     default: False;
	  endcase;
endfunction

// ================================================================

endpackage
