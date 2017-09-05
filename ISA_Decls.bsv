// Copyright (c) 2013-2017 Bluespec, Inc. All Rights Reserved

// ================================================================
// ISA defs for UC Berkeley RISC V
//
// References (from riscv.org):
//   "The RISC-V Instruction Set Manual
//    Volume I: User-Level ISA, Version 2.0, May 6, 2014"
//
//   "The RISC-V Instruction Set Manual
//    Volume II: Privileged Architecture, Version 1.9.1, Nov 4, 2016"
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
typedef TSub #(XLEN, 2)  XLEN_MINUS_2;// XLEN-2 for MTVEC base width

Integer xlen = valueOf (XLEN);

typedef enum { RV32, RV64 } RV_Version deriving (Eq, Bits);

RV_Version rv_version = ( (valueOf (XLEN) == 32) ? RV32 : RV64 );

// ----------------

typedef  Bit #(XLEN)  Word;      // Raw (unsigned) register data
typedef  Int #(XLEN)  Word_S;    // Signed register data
typedef  Word         Addr;      // addresses/pointers

// ----------------

typedef  8                                     Bits_per_Byte;
typedef  Bit #(Bits_per_Byte)                  Byte;

typedef  XLEN                                  Bits_per_Word;
typedef  TDiv #(Bits_per_Word, Bits_per_Byte)  Bytes_per_Word;
typedef  TLog #(Bytes_per_Word)                Bits_per_Byte_in_Word;
typedef  Bit #(Bits_per_Byte_in_Word)          Byte_in_Word;

typedef  Vector #(Bytes_per_Word, Byte)        Word_B;

typedef  XLEN                                  Bits_per_Addr;
typedef  TDiv #(Bits_per_Addr, Bits_per_Byte)  Bytes_per_Addr;

Integer  bits_per_byte         = valueOf (Bits_per_Byte);
Integer  bytes_per_word        = valueOf (Bytes_per_Word);
Integer  bits_per_byte_in_word = valueOf (Bits_per_Byte_in_Word);

Integer  addr_lo_byte_in_word = 0;
Integer  addr_hi_byte_in_word = addr_lo_byte_in_word + bits_per_byte_in_word - 1;

function  Byte_in_Word  fn_addr_to_byte_in_word (Addr a);
   return a [addr_hi_byte_in_word : addr_lo_byte_in_word ];
endfunction

// ----------------
// can have one or two fpu sizes (should they be merged sooner than later ?)
Bool hasFpu32 = True;
Bool hasFpu64 = True;

typedef  64  FLEN;                          // For RV{32,64}D

typedef  Bit #(FLEN) FP_Value;

// ================================================================
// Tokens are used for signalling/synchronization, and have no payload

typedef Bit #(0) Token;

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

RegName reg_zero =  0;
RegName reg_ra   =  1;
RegName reg_sp   =  2;
RegName reg_gp   =  3;
RegName reg_tp   =  4;

RegName reg_t0   =  5; RegName reg_t1  =  6; RegName reg_t2 =  7;
RegName reg_fp   =  8;
RegName reg_s0   =  8; RegName reg_s1  =  9;

RegName reg_a0   = 10; RegName reg_a1  = 11;
RegName reg_v0   = 10; RegName reg_v1  = 11;

RegName reg_a2   = 12; RegName reg_a3  = 13; RegName reg_a4 = 14; RegName reg_a5 = 15;
RegName reg_a6   = 16; RegName reg_a7  = 17;

RegName reg_s2   = 18; RegName reg_s3  = 19; RegName reg_s4 = 20; RegName reg_s5 = 21;
RegName reg_s6   = 22; RegName reg_s7  = 23; RegName reg_s8 = 24; RegName reg_s9 = 25;
RegName reg_s10  = 26; RegName reg_s11 = 27;

RegName reg_t3   = 28; RegName reg_t4  = 29; RegName reg_t5 = 30; RegName reg_t6 = 31;

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

typedef struct {
   // Predecessors
   Bool pi;    // IO reads
   Bool po;    // IO writes
   Bool pr;    // Mem reads
   Bool pw;    // Mem writes
   // Successors
   Bool si;
   Bool so;
   Bool sr;
   Bool sw;
   } Fence_Ordering
deriving (FShow);

instance Bits #(Fence_Ordering, 8);
   function Bit #(8) pack (Fence_Ordering fo);
      return {pack (fo.pi),
	      pack (fo.po),
	      pack (fo.pr),
	      pack (fo.pw),
	      pack (fo.si),
	      pack (fo.so),
	      pack (fo.sr),
	      pack (fo.sw) };
   endfunction
   function Fence_Ordering unpack (Bit #(8) b8);
      return Fence_Ordering {pi: unpack (b8 [7]),
			     po: unpack (b8 [6]),
			     pr: unpack (b8 [5]),
			     pw: unpack (b8 [4]),
			     si: unpack (b8 [3]),
			     so: unpack (b8 [2]),
			     sr: unpack (b8 [1]),
			     sw: unpack (b8 [0]) };
   endfunction
endinstance

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

// sub-opcodes: (in funct3 field)
Bit #(3)   f3_PRIV           = 3'b000;
Bit #(3)   f3_CSRRW          = 3'b001;
Bit #(3)   f3_CSRRS          = 3'b010;
Bit #(3)   f3_CSRRC          = 3'b011;
Bit #(3)   f3_SYSTEM_ILLEGAL = 3'b100;
Bit #(3)   f3_CSRRWI         = 3'b101;
Bit #(3)   f3_CSRRSI         = 3'b110;
Bit #(3)   f3_CSRRCI         = 3'b111;

// sub-sub-opcodes for f3_PRIV

Bit #(12) f12_ECALL     = 12'b_0000_0000_0000;
Bit #(12) f12_EBREAK    = 12'b_0000_0000_0001;

Bit #(12) f12_URET      = 12'b_0000_0000_0010;
Bit #(12) f12_SRET      = 12'b_0001_0000_0010;
Bit #(12) f12_HRET      = 12'b_0010_0000_0010;
Bit #(12) f12_MRET      = 12'b_0011_0000_0010;
Bit #(12) f12_WFI       = 12'b_0001_0000_0101;

// v1.10 sub-sub-opcode for SFENCE_VMA
Bit #(7)  f7_SFENCE_VMA = 7'b_0001_001;

Instr break_instr = { f12_EBREAK, 5'b00000, 3'b000, 5'b00000, op_SYSTEM };

function Bool f3_is_CSRR_any (Bit #(3) f3);
   return (f3 [1:0] != 2'b00);
endfunction

function Bool f3_is_CSRR_W (Bit #(3) f3);
   return (f3 [1:0] == 2'b01);
endfunction

function Bool f3_is_CSRR_S_or_C (Bit #(3) f3);
   return (f3 [1] == 1'b1);
endfunction

// ================================================================
// Privilege Modes

typedef 4 Num_Priv_Modes;

typedef Bit #(2) Priv_Mode;

Priv_Mode  u_Priv_Mode = 2'b00;
Priv_Mode  s_Priv_Mode = 2'b01;
Priv_Mode  m_Priv_Mode = 2'b11;

function Fmt fshow_Priv_Mode (Priv_Mode pm);
   return case (pm)
	     u_Priv_Mode: $format ("U");
	     s_Priv_Mode: $format ("S");
	     m_Priv_Mode: $format ("M");
	     default: $format ("RESERVED");
	  endcase;
endfunction

// ================================================================
// Control/Status registers

typedef Bit #(12) CSR_Addr;

// ----------------
// User-level CSR addresses

CSR_Addr   csr_ustatus        = 12'h000;    // User status
CSR_Addr   csr_uie            = 12'h004;    // User interrupt-enable
CSR_Addr   csr_utvec          = 12'h005;    // User trap handler base address

CSR_Addr   csr_uscratch       = 12'h040;    // Scratch register for trap handlers
CSR_Addr   csr_uepc           = 12'h041;    // User exception program counter
CSR_Addr   csr_ucause         = 12'h042;    // User trap cause
CSR_Addr   csr_ubadaddr       = 12'h043;    // User bad address
CSR_Addr   csr_uip            = 12'h044;    // User interrupt pending

CSR_Addr   csr_fflags         = 12'h001;    // Floating-point accrued exceptions
CSR_Addr   csr_frm            = 12'h002;    // Floating-point Dynamic Rounding Mode
CSR_Addr   csr_fcsr           = 12'h003;    // Floating-point Control and Status Register (frm + fflags)

CSR_Addr   csr_cycle          = 12'hC00;    // Cycle counter for RDCYCLE
CSR_Addr   csr_time           = 12'hC01;    // Timer for RDTIME
CSR_Addr   csr_instret        = 12'hC02;    // Instructions retired counter for RDINSTRET

CSR_Addr   csr_hpmcounter3    = 12'hC03;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter4    = 12'hC04;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter5    = 12'hC05;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter6    = 12'hC06;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter7    = 12'hC07;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter8    = 12'hC08;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter9    = 12'hC09;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter10   = 12'hC0A;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter11   = 12'hC0B;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter12   = 12'hC0C;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter13   = 12'hC0D;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter14   = 12'hC0E;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter15   = 12'hC0F;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter16   = 12'hC10;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter17   = 12'hC11;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter18   = 12'hC12;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter19   = 12'hC13;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter20   = 12'hC14;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter21   = 12'hC15;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter22   = 12'hC16;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter23   = 12'hC17;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter24   = 12'hC18;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter25   = 12'hC19;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter26   = 12'hC1A;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter27   = 12'hC1B;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter28   = 12'hC1C;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter29   = 12'hC1D;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter30   = 12'hC1E;    // Performance-monitoring counter
CSR_Addr   csr_hpmcounter31   = 12'hC1F;    // Performance-monitoring counter

CSR_Addr   csr_cycleh         = 12'hC80;    // Upper 32 bits of csr_cycle (RV32I only)
CSR_Addr   csr_timeh          = 12'hC81;    // Upper 32 bits of csr_time (RV32I only)
CSR_Addr   csr_instreth       = 12'hC82;    // Upper 32 bits of csr_instret (RV32I only)

CSR_Addr   csr_hpmcounter3h   = 12'hC83;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter4h   = 12'hC84;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter5h   = 12'hC85;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter6h   = 12'hC86;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter7h   = 12'hC87;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter8h   = 12'hC88;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter9h   = 12'hC89;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter10h  = 12'hC8A;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter11h  = 12'hC8B;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter12h  = 12'hC8C;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter13h  = 12'hC8D;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter14h  = 12'hC8E;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter15h  = 12'hC8F;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter16h  = 12'hC90;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter17h  = 12'hC91;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter18h  = 12'hC92;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter19h  = 12'hC93;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter20h  = 12'hC94;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter21h  = 12'hC95;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter22h  = 12'hC96;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter23h  = 12'hC97;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter24h  = 12'hC98;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter25h  = 12'hC99;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter26h  = 12'hC9A;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter27h  = 12'hC9B;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter28h  = 12'hC9C;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter29h  = 12'hC9D;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter30h  = 12'hC9E;    // Upper 32 bits of performance-monitoring counter
CSR_Addr   csr_hpmcounter31h  = 12'hC9F;    // Upper 32 bits of performance-monitoring counter

// ================================================================
// Supervisor-Level ISA defs

// `include "ISA_Decls_Priv_S.bsv"

// ================================================================
// Hypervisor-Level ISA defs

// `include "ISA_Decls_Priv_H.bsv"

// ================================================================
// Machine-Level ISA defs

`include "ISA_Decls_Priv_M.bsv"

// ================================================================
// TODO: The following are not really ISA-specification defs; should not be in this file.
// ================================================================
// The following is tighter encoding of the DMem operation codes
// DCache operations (TODO: add Fences, AMOs)

typedef enum { DCACHE_R, DCACHE_W } DCacheOp
deriving (Bits, Eq, FShow);

// ================================================================
// For tandem verifier

// The CPU sends out a stream of these packets to a "tandem verifier".
// A tandem verifier is a "golden reference" ISA simulator, such as:
//   - Bluespec's Cissr (written in C)
//   - Bluespec's BluROCS (written in BSV, and synthesizable)
//   - Berkeley's Spike (written in C/C++)
//   - SRI's RISC-V formal spec (written in the L3 specification language)

// When the CPU implementation is running code, it send out InstructionRetire
// packets describing each retired instruction, so that the tandem verifier
// can check that the implementation is doing the right thing.
// These packets describe all the possible side-effects of an instruction.

// Packets with the other commands (Reset, Write{Memory/GPR/CSR/FPR/FSR/PC})
// are sent in other (non-running) situations when the CPU modifies its state,
// e.g., in response to GDB commands, to keep the TandemVerifier state in sync
// with the implementation.


typedef enum {
   InstructionRetire = 0,
   Reset,
   WriteMemory,
   WriteGPR,
   WriteCSR,
   WriteFPR,
   WriteFSR,
   WritePC
   } ForVerifier_Cmd
   deriving (Bits, Eq, FShow);

typedef struct {
   ForVerifier_Cmd  cmd;

   Bool  exc_taken;   // Exception taken (interrupt or trap)

   Word  pc;          // Of this instr (on exception this is same as new csr_epc)

   Word  addr;        // Exception branch, jump, xRET: new PC
                      // Mem ops and AMOs: mem addr
                      // CSRR{S,C,W}: CSR addr

   Word  data1;       // ALU ops, LOAD, LOAD_FP, LR, SC, CSRR{S,C,W}: new rd_val
                      // Exceptions and xRET: new csr_mstatus

   Word  data2;       // Exceptions: new csr_cause
                      // STORE, STORE_FP, SC, AMO: new mem val
                      // CSRR{S,C,W}: new CSR val

   Word  data3;       // Instruction

   FP_Value  fpdata;  // Floating point result

   int       verbosity;
   } Info_CPU_to_Verifier
deriving (Bits, FShow);

instance DefaultValue #(Info_CPU_to_Verifier);
   defaultValue = unpack (0);
endinstance

// ================================================================

endpackage
