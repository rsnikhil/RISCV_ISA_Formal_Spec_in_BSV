// Copyright (c) 2016-2017 Bluespec, Inc.  All Rights Reserved.
// Author: Rishiyur S. Nikhil

// This is a formal specification of the RISC-V ISA, given as an
// executable BSV module representing a RISC-V CPU.
// The module's parameters are:
//  - an interface to memory,
//  - booleans from an external oracle indicating external
//      non-deterministic events (interrupts, when to increment cycle
//      count, etc.)

// Although much of ISA semantics can be written as a single function,
// we deliberately break some activities into split-phase actions so
// that this model can be directly plugged into environments that
// actually model/implement delays for those activities, and
// non-deterministic interleavings of such activities when there are
// multiple cores (multiple copies of this ISA spec).
// Examples of such split-phase actions:
//    - Instruction fetch
//    - Data memory accesses
//    - Fences

// This code is executable (and has been executed on numerous RISC-V
// ELF binaries).  Execution normally uses simulation (Bluespec's
// Bluesim simulator for BSV).  However, it can also be compiled into
// synthesizable Verilog, which can be executed in a Verilog simulator
// or on an FPGA.

package RISCV_Spec;

// ================================================================
// BSV library imports

import GetPut       :: *;
import ClientServer :: *;

// ----------------
// BSV additional libs

import Cur_Cycle   :: *;

// ================================================================
// BSV project imports

import ISA_Decls :: *;    // Instruction encodings
import RegFiles  :: *;    // GPRs and CSRs

import IntMulDivRem_ALU :: *;

// ================================================================
// Memory interface for CPU

// ----------------
// IMem responses: either and exception or an instruction

typedef union tagged {
   Exc_Code  IMem_Resp_Exception;
   Word      IMem_Resp_Ok;
   } IMem_Resp
deriving (FShow);

// ----------------
// DMem request ops and sizes

typedef enum { MEM_OP_LOAD, MEM_OP_STORE } Mem_Op
deriving (Eq, FShow);

// ----------------
// DMem requests

typedef struct {
   Mem_Op         mem_op;
   Mem_Data_Size  mem_data_size;
   Addr           addr;
   Word           store_value;    // Only relevant if mem_op == MEM_OP_STORE
   } DMem_Req
deriving (FShow);

// ----------------
// DMem responses: either an exception or data
// (data value is only relevant for LOADs, irrelevant for STOREs)

typedef union tagged {
   Exc_Code  DMem_Resp_Exception;
   Word      DMem_Resp_Ok;
   } DMem_Resp
deriving (FShow);

// ----------------------------------------------------------------
// This interface is an argument to the 'mkRISCV_Spec' module,
// and is used inside the module to access memory.
// MMUs, caches etc. are behind this interface.

interface Memory_IFC;
   // Instruction memory
   method Action                   imem_req (Addr addr);
   method ActionValue #(IMem_Resp) imem_resp;

   // Data memory
   method    Action                          dmem_req (DMem_Req req);
   method    ActionValue #(DMem_Resp)        dmem_resp;
   interface Server #(Token, Token)          server_fence_i;
   interface Server #(Fence_Ordering, Token) server_fence;
endinterface

// ================================================================
// This is the external interface of the 'mkRISCV_Spec' module.
// It is not part of the spec, per se, and just represents an API that
// allows the environment to control the CPU and probe its state.

interface RISCV_Spec_IFC;
   // Reset
   method Action reset;

   // Run control
   method Action start;
   method Action step;
   method Bool   stopped;
   method Action gdb_stop_req;

   // Continuous signal from external interrupt controller
   //   m_exc_code == tagged Invalid   => no interrupt pending
   //   m_exc_code == tagged Valid ec  => interrupt pending with ec exception code
   (* always_ready, always_enabled *)
   method Action interrupt_req (Maybe #(Exc_Code) m_exc_code);

   // Non-deterministic external request to increment "CYCLE" counter
   method Action incr_cycle;

   // Debugger access to architectural state
   method Word   read_gpr  (RegName r);
   method Action write_gpr (RegName r, Word value);

   method Word   read_pc;
   method Action write_pc  (Addr pc_value);

   method Maybe #(Word) read_csr  (CSR_Addr csr_addr);
   method Action        write_csr (CSR_Addr csr_addr, Word csr_value);
endinterface

// ================================================================
// The RISC-V CPU Specification module, 'mkRISCV_Spec'

// ----------------
// The CPU is initially in the IDLE state.
// It starts running when it is put into the FETCH state.
// When running, it cycles through the following sequences of states:
//
//     FETCH -> EXEC                             for most instructions
//     FETCH -> EXEC -> EXEC_LD_RESPONSE         for LD instructions
//     FETCH -> EXEC -> EXEC_ST_RESPONSE         for ST instructions
//     FETCH -> EXEC -> EXEC_FENCE_I_RESPONSE    for FENCE.I instructions
//     FETCH -> EXEC -> EXEC_FENCE_RESPONSE      for FENCE instructions
//     FETCH -> EXEC -> WFI                      for WFI instruction

typedef enum {STATE_IDLE,
	      STATE_FETCH,
	      STATE_EXEC,
	      STATE_EXEC_LD_RESPONSE,
	      STATE_EXEC_ST_RESPONSE,
	      STATE_EXEC_FENCE_I_RESPONSE,
	      STATE_EXEC_FENCE_RESPONSE,
	      STATE_WFI
   } CPU_STATE
deriving (Eq, Bits, FShow);

// ----------------
// Default fall-through PC

function Addr fv_fall_through_pc (Addr pc);
   return pc + 4;
endfunction: fv_fall_through_pc

// ----------------

module mkRISCV_Spec #(RegFiles_IFC regfiles,          // interface to GPR and CSR regs
		      Memory_IFC   memory,            // interface to instr and data memories
		      Word         pc_reset_value,
		      Bit #(4)     cfg_verbosity)     // of info messages during execution
                    (RISCV_Spec_IFC);

   // Program counter
   Reg #(Word) pc <- mkRegU;

   // Current privilege level
   Reg #(Priv_Mode) rg_cur_priv <- mkRegU;

   IntMulDivRem_ALU_IFC intMulDivRem_ALU <- mkIntMulDivRem_ALU;

   // ----------------
   // Non-architectural state, for this model

   Reg #(CPU_STATE) cpu_state   <- mkReg (STATE_IDLE);
   Reg #(Addr)      rg_mem_addr <- mkRegU;    // Effective addr in LD/ST
   Reg #(Word)      rg_instr    <- mkRegU;    // Current instruction

   // Connect gdb-stop request interface method to rules
   Reg #(Bool) rg_gdb_stop_req <- mkReg (False);
   Reg #(Bool) rg_gdb_step_req <- mkReg (False);

   // Connect external interrupt request interface method to rules
   Reg #(Maybe #(Exc_Code)) rg_interrupt_req <- mkReg (tagged Invalid);

   // ================================================================
   // Instruction execution

   // ----------------------------------------------------------------
   // The following functions are common idioms for finishing an instruction

   // ----------------
   // Finish "normal" instr:
   //  - write Rd (if instr has Rd)
   //  - incr instret
   //  - incr PC
   //  - goto FETCH state

   function Action fa_finish_normal (Maybe #(Tuple2 #(RegName, Word)) maybe_rd_rdval);
      action
	 if (cfg_verbosity > 1)
	    $display ("RISCV_Spec.fa_finish_normal: ", fshow (maybe_rd_rdval));

	 // Write Rd if present and not reg 0
	 if (maybe_rd_rdval matches tagged Valid { .rd, .rd_val })
	    if (rd != 0)
	       regfiles.write_rd (rd, rd_val);

	 regfiles.csr_instret_incr;

	 pc <= fv_fall_through_pc (pc);

	 cpu_state <= STATE_FETCH;
      endaction
   endfunction

   // ----------------
   // Finish csrrx instr: same as "normal", except:
   //  - incr instret if it was not written the csrrx instruction

   function Action fa_finish_csrrx (Maybe #(Tuple2 #(RegName, Word)) maybe_rd_rdval,
				    Bool                             wrote_instret);
      action
	 if (cfg_verbosity > 1) begin
	    $display ("RISCV_Spec.fa_finish_csrrx: ", fshow (maybe_rd_rdval));
	    if (wrote_instret)
	       $display ("    Not incrementing instret");
	 end

	 // Write Rd if present and not reg 0
	 if (maybe_rd_rdval matches tagged Valid { .rd, .rd_val })
	    if (rd != 0)
	       regfiles.write_rd (rd, rd_val);

	 if (! wrote_instret)
	    regfiles.csr_instret_incr;

	 pc <= fv_fall_through_pc (pc);

	 cpu_state <= STATE_FETCH;
      endaction
   endfunction

   // ----------------
   // Finish conditional branch instr: incr instret, set PC, go to FETCH state

   function Action fa_finish_cond_branch (Bool branch_taken, Addr next_pc);
      action
	 if (cfg_verbosity > 1)
	    $display ("RISCV_Spec.fa_finish_cond_branch: Taken %0d, pc 0x%0h, next_pc 0x%0h",
		      pack (branch_taken), pc, next_pc);

	 regfiles.csr_instret_incr;
	 pc <= (branch_taken ? next_pc : fv_fall_through_pc (pc));
	 cpu_state <= STATE_FETCH;
      endaction
   endfunction

   // ----------------
   // Finish jump instrs; write Rd, incr instret, set PC, go to FETCH state

   function Action fa_finish_jump (RegName rd, Word rd_value, Addr next_pc);
      action
	 if (cfg_verbosity > 1)
	    $display ("RISCV_Spec.fa_finish_jump: Rd 0x%0h, value 0x%0h, next_pc 0x%0h",
		      rd, rd_value, next_pc);

	 if (rd != 0)
	    regfiles.write_rd (rd, rd_value);

	 regfiles.csr_instret_incr;
	 pc <= next_pc;

	 cpu_state <= STATE_FETCH;
      endaction
   endfunction

   // ----------------
   // Finish trap

   function Action fa_finish_trap (Word epc, Exc_Code exc_code, Addr badaddr);
      action
	 // Special case: BREAK in m-mode takes us into a GDB debug stop
	 if (   (rg_cur_priv == m_Priv_Mode)
	     && (exc_code == exc_code_BREAKPOINT))
	    begin
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_finish_trap: GDB BREAK at PC 0x%08h", pc);
	       cpu_state <= STATE_IDLE;
	    end

	 // Normal case
	 else begin
	    if ((cfg_verbosity != 0) || (exc_code == exc_code_ILLEGAL_INSTRUCTION))
	       $display ("RISCV_Spec.fa_finish_trap: epc = 0x%0h, exc_code = 0x%0h, badaddr = 0x%0h",
			 epc, exc_code, badaddr);

	    match {.next_pc,
		   .new_mstatus,
		   .mcause }     <- regfiles.csr_trap_actions (rg_cur_priv,    // from priv
							       m_Priv_Mode,    // to priv
							       epc,
							       False,          // not an interrupt,
							       exc_code,
							       badaddr);
	    pc          <= next_pc;
	    rg_cur_priv <= m_Priv_Mode;

	    // Accounting: increment instret if ECALL
	    // TODO: is this ok? ECALL is the only trapping instr that "completes".
	    if (   (exc_code >= exc_code_ECALL_FROM_U)
	       && (exc_code <= exc_code_ECALL_FROM_M))
	       regfiles.csr_instret_incr;

	    cpu_state <= STATE_FETCH;
	 end
      endaction
   endfunction

   // ----------------
   // Finish interrupt

   function Action fa_finish_interrupt (Word epc, Exc_Code exc_code);
      action
	 if ((cfg_verbosity != 0) || (exc_code == exc_code_ILLEGAL_INSTRUCTION))
	    $display ("RISCV_Spec.fa_finish_interrupt: epc = 0x%0h, exc_code = 0x%0h",
		      epc, exc_code);

	 match {.next_pc,
		.new_mstatus,
		.mcause }     <- regfiles.csr_trap_actions (rg_cur_priv,    // from priv
							    m_Priv_Mode,    // to priv
							    epc,
							    True,           // interrupt,
							    exc_code,
							    ?);
	 rg_cur_priv <= m_Priv_Mode;

	 cpu_state   <= STATE_FETCH;
      endaction
   endfunction

   // ----------------
   // Finish WFI: incr instret, set PC, go to WFI state

   function Action fa_finish_WFI;
      action
	 if (cfg_verbosity > 1)
	    $display ("RISCV_Spec.fa_finish_WFI");

	 regfiles.csr_instret_incr;
	 pc <= fv_fall_through_pc (pc);
	 cpu_state <= STATE_WFI;
      endaction
   endfunction

   // ----------------------------------------------------------------
   // Instruction execution
   // This function encapsulates ALL the opcodes.
   // It has internal functions that group related sub-opcodes.

   function Action fa_exec (Instr instr);
      action
	 // ----------------------------------------------------------------
	 // Instruction decode

	 Decoded_Instr decoded = fv_decode (instr);

	 // Values of Rs1 and Rs2 fields of the instr, unsigned
	 Word    v1   = ((decoded.rs1 == 0) ? 0: regfiles.read_rs1 (decoded.rs1));
	 Word    v2   = ((decoded.rs2 == 0) ? 0: regfiles.read_rs2 (decoded.rs2));

	 // Values of Rs1 and Rs2 fields of the instr, signed versions
	 Word_S  s_v1 = unpack (v1);
	 Word_S  s_v2 = unpack (v2);

	 // 32b versions of the above, For 32b instrs in RV64I
	 Bit #(32)  v1_32   = truncate (v1);
	 Bit #(32)  v2_32   = truncate (v2);
	 Int #(32)  s_v1_32 = unpack (v1_32);
	 Int #(32)  s_v2_32 = unpack (v2_32);

	 // Value of CSR field of instr (if a valid CSR address)
	 Maybe #(Word) m_v_csr = regfiles.read_csr (decoded.csr);

	 // ----------------------------------------------------------------
	 // Upper Immediate instructions

	 function Action fa_exec_LUI ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_LUI");

	       Bit #(32)  v32   = { decoded.imm20_U, 12'h0 };
	       Word_S     iv    = extend (unpack (v32));
	       let        value = pack (iv);

	       fa_finish_normal (tagged Valid (tuple2 (decoded.rd, value)));
	    endaction
	 endfunction: fa_exec_LUI

	 function Action fa_exec_AUIPC ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_AUIPC");

	       Word_S  iv    = extend (unpack ({ decoded.imm20_U, 12'b0}));
	       Word_S  pc_s  = unpack (pc);
	       Word    value = pack (pc_s + iv);

	       fa_finish_normal (tagged Valid (tuple2 (decoded.rd, value)));
	    endaction
	 endfunction: fa_exec_AUIPC

	 // ----------------------------------------------------------------
	 // Control-transfer instructions (branch and jump)

	 function Action fa_exec_JAL ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_JAL");

	       Word_S offset  = extend (unpack (decoded.imm21_UJ));
	       Addr   next_pc = pack (unpack (pc) + offset);

	       fa_finish_jump (decoded.rd, fv_fall_through_pc (pc), next_pc);
	    endaction
	 endfunction: fa_exec_JAL

	 function Action fa_exec_JALR ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_JALR");

	       Word_S offset  = extend (unpack (decoded.imm12_I));
	       Addr   next_pc = pack (s_v1 + offset);

	       fa_finish_jump (decoded.rd, fv_fall_through_pc (pc), next_pc);
	    endaction
	 endfunction: fa_exec_JALR

	 function Action fa_exec_BRANCH ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_BRANCH");

	       Word_S offset  = extend (unpack (decoded.imm13_SB));
	       Word   next_pc = pack (unpack (pc) + offset);

	       if      (decoded.funct3 == f3_BEQ)  fa_finish_cond_branch (v1  == v2,    next_pc);
	       else if (decoded.funct3 == f3_BNE)  fa_finish_cond_branch (v1  != v2,    next_pc);
	       else if (decoded.funct3 == f3_BLT)  fa_finish_cond_branch (s_v1 <  s_v2, next_pc);
	       else if (decoded.funct3 == f3_BGE)  fa_finish_cond_branch (s_v1 >= s_v2, next_pc);
	       else if (decoded.funct3 == f3_BLTU) fa_finish_cond_branch (v1  <  v2,    next_pc);
	       else if (decoded.funct3 == f3_BGEU) fa_finish_cond_branch (v1  >= v2,    next_pc);
	       else fa_finish_trap (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
	    endaction
	 endfunction: fa_exec_BRANCH

	 // ----------------------------------------------------------------
	 // LD and ST instructions.
	 // Issue request here; will be completed in STATE_EXEC_LD/ST_RESPONSE

	 function Action fa_exec_LD_req ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_LD_req");

	       Word_S  imm_s    = extend (unpack (decoded.imm12_I));
	       Word    mem_addr = pack (s_v1 + imm_s);

	       function Action fa_LD_Req (Mem_Data_Size sz);
		  action
		     let req = DMem_Req {mem_op:        MEM_OP_LOAD,
					 mem_data_size: sz,
					 addr:          mem_addr,
					 store_value:   ?};
		     memory.dmem_req (req);
		     cpu_state <= STATE_EXEC_LD_RESPONSE;
		  endaction
	       endfunction

	       rg_mem_addr <= mem_addr;

	       if      (decoded.funct3 == f3_LB)                    fa_LD_Req (BITS8);
	       else if (decoded.funct3 == f3_LBU)                   fa_LD_Req (BITS8);
	       else if (decoded.funct3 == f3_LH)                    fa_LD_Req (BITS16);
	       else if (decoded.funct3 == f3_LHU)                   fa_LD_Req (BITS16);
	       else if (decoded.funct3 == f3_LW)                    fa_LD_Req (BITS32);
	       else if ((decoded.funct3 == f3_LWU) && (xlen == 64)) fa_LD_Req (BITS32);
	       else if ((decoded.funct3 == f3_LD)  && (xlen == 64)) fa_LD_Req (BITS64);
	       else fa_finish_trap (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
	    endaction
	 endfunction: fa_exec_LD_req

	 function Action fa_exec_ST_req ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_ST_req");

	       Word_S  imm_s    = extend (unpack (decoded.imm12_S));
	       Word    mem_addr = pack (s_v1 + imm_s);

	       function Action fa_ST_req (Mem_Data_Size sz);
		  action
		     let req = DMem_Req {mem_op:        MEM_OP_STORE,
					 mem_data_size: sz,
					 addr:          mem_addr,
					 store_value:   v2};
		     memory.dmem_req (req);
		     cpu_state <= STATE_EXEC_ST_RESPONSE;
		  endaction
	       endfunction

	       rg_mem_addr <= mem_addr;

	       if      (decoded.funct3 == f3_SB)                   fa_ST_req (BITS8);
	       else if (decoded.funct3 == f3_SH)                   fa_ST_req (BITS16);
	       else if (decoded.funct3 == f3_SW)                   fa_ST_req (BITS32);
	       else if ((decoded.funct3 == f3_SD) && (xlen == 64)) fa_ST_req (BITS64);
	       else fa_finish_trap (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
	    endaction
	 endfunction: fa_exec_ST_req

	 // ----------------------------------------------------------------
	 // Register-Immediate instructions

	 function Action fa_exec_OP_IMM ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_OP_IMM");

	       Word                v2    = zeroExtend (decoded.imm12_I);
	       Word_S              s_v2  = signExtend (unpack (decoded.imm12_I));
	       Bit #(TLog #(XLEN)) shamt = truncate (decoded.imm12_I);

	       if      (decoded.funct3 == f3_ADDI)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, pack (s_v1 + s_v2))));

	       else if (decoded.funct3 == f3_SLTI)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, ((s_v1 < s_v2) ? 1 : 0))));

	       else if (decoded.funct3 == f3_SLTIU)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, ((v1  < v2)  ? 1 : 0))));

	       else if (decoded.funct3 == f3_XORI)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, pack (s_v1 ^ s_v2))));

	       else if (decoded.funct3 == f3_ORI)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, pack (s_v1 | s_v2))));

	       else if (decoded.funct3 == f3_ANDI)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, pack (s_v1 & s_v2))));

	       else if (   (decoded.funct3 == f3_SLLI)
			&& (   ((xlen == 32) && (instr [31:25] == 7'b000_0000))
			    || ((xlen == 64) && (instr [31:26] == 6'b000_000 ))))
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, (v1 << shamt))));


	       // SRLI
	       else if (   (decoded.funct3 == f3_SRxI)
			&& (   ((xlen == 32) && (instr [31:25] == 7'b000_0000))
			    || ((xlen == 64) && (instr [31:26] == 6'b000_000 ))))
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, (v1 >> shamt))));

	       // SRAI
	       else if (   (decoded.funct3 == f3_SRxI)
			&& (   ((xlen == 32) && (instr [31:25] == 7'b010_0000))
			    || ((xlen == 64) && (instr [31:26] == 6'b010_000 ))))
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, pack (s_v1 >> shamt))));

	       else 
		  fa_finish_trap (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
	    endaction
	 endfunction: fa_exec_OP_IMM

	 // ----------------------------------------------------------------
	 // Register-Register instructions

	 function Action fa_exec_OP ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_OP");

	       Bit #(TLog #(XLEN)) shamt = truncate (v2);    // Caveat: upper bits are unspecified, per spec doc

	       if      (decoded.funct10 == f10_ADD)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, pack (s_v1 + s_v2))));

	       else if (decoded.funct10 == f10_SUB)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, pack (s_v1 - s_v2))));

	       else if (decoded.funct10 == f10_SLL)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, (v1 << shamt))));

	       else if (decoded.funct10 == f10_SLT)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, ((s_v1 < s_v2) ? 1 : 0))));

	       else if (decoded.funct10 == f10_SLTU)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, ((v1  < v2)  ? 1 : 0))));

	       else if (decoded.funct10 == f10_XOR)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, pack (s_v1 ^ s_v2))));

	       else if (decoded.funct10 == f10_SRL)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, (v1 >> shamt))));

	       else if (decoded.funct10 == f10_SRA)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, pack (s_v1 >> shamt))));

	       else if (decoded.funct10 == f10_OR)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, pack (s_v1 | s_v2))));

	       else if (decoded.funct10 == f10_AND)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, pack (s_v1 & s_v2))));

`ifdef ISA_M
	       // ----------------
	       // 'M' instructions

	       else if (decoded.funct10 == f10_MUL) begin
		  let v_rd <- intMulDivRem_ALU.m_MUL (v1, v2);
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, v_rd)));
	       end

	       else if (decoded.funct10 == f10_MULH) begin
		  let v_rd <- intMulDivRem_ALU.m_MULH (v1, v2);
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, v_rd)));
	       end

	       else if (decoded.funct10 == f10_MULHU) begin
		  let v_rd <- intMulDivRem_ALU.m_MULHU (v1, v2);
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, v_rd)));
	       end

	       else if (decoded.funct10 == f10_MULHSU) begin
		  let v_rd <- intMulDivRem_ALU.m_MULHSU (v1, v2);
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, v_rd)));
	       end

	       else if (decoded.funct10 == f10_DIV) begin
		  let v_rd <- intMulDivRem_ALU.m_DIV (v1, v2);
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, v_rd)));
	       end

	       else if (decoded.funct10 == f10_DIVU) begin
		  let v_rd <- intMulDivRem_ALU.m_DIVU (v1, v2);
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, v_rd)));
	       end

	       else if (decoded.funct10 == f10_REM) begin
		  let v_rd <- intMulDivRem_ALU.m_REM (v1, v2);
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, v_rd)));
	       end

	       else if (decoded.funct10 == f10_REMU) begin
		  let v_rd <- intMulDivRem_ALU.m_REM (v1, v2);
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, v_rd)));
	       end
`endif

	       else
		  fa_finish_trap (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
	    endaction
	 endfunction: fa_exec_OP

	 // ----------------------------------------------------------------
	 // The following OP_IMM_32 and OP_32 sections are for 32b
	 // instructions valid only in RV64

	 // ----------------------------------------------------------------
	 // Register-Immediate 32b instructions in RV64

	 function Action fa_exec_OP_IMM_32 ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_OP_IMM_32");

	       Word                v2    = zeroExtend (decoded.imm12_I);
	       Word_S              s_v2  = signExtend (unpack (decoded.imm12_I));
	       Bit #(TLog #(XLEN)) shamt = truncate (decoded.imm12_I);

	       if (decoded.funct3 == f3_ADDIW) begin
		  Int #(32) s_v2_32 = signExtend (unpack (decoded.imm12_I));
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd,
							  pack (signExtend ((s_v1_32 + s_v2_32))))));
	       end

	       else if (   (decoded.funct3 == f3_SLLIW)
			&& (instr [31:25] == 7'b000_0000))
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, signExtend (v1_32 << shamt))));

	       // SRLIW
	       else if (   (decoded.funct3 == f3_SRxIW)
			&& (instr [31:25] == 7'b000_0000))
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, signExtend (v1_32 >> shamt))));

	       // SRAIW
	       else if (   (decoded.funct3 == f3_SRxIW)
			&& (instr [31:25] == 7'b010_0000))
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd,
							  signExtend (pack (s_v1_32 >> shamt)))));

	       else
		  fa_finish_trap (pc, exc_code_ILLEGAL_INSTRUCTION, ?);

	    endaction
	 endfunction

	 // ----------------------------------------------------------------
	 // Register-Register 32b instructions in RV64

	 function Action fa_exec_OP_32 ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_OP_32");

	       Bit #(TLog #(XLEN)) shamt = truncate (v2);    // Caveat: upper bits are unspecified, per spec doc

	       if (decoded.funct10 == f10_ADDW)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd,
							  pack (signExtend (s_v1_32 + s_v2_32)))));

	       else if (decoded.funct10 == f10_SUBW)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd,
							  pack (signExtend (s_v1_32 - s_v2_32)))));

	       else if (decoded.funct10 == f10_SLLW)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd,
							  pack (signExtend (v1_32 << shamt)))));

	       else if (decoded.funct10 == f10_SRLW)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd,
							  pack (signExtend (v1_32 >> shamt)))));

	       else if (decoded.funct10 == f10_SRAW)
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd,
							  pack (signExtend (s_v1_32 >> shamt)))));
	       // ----------------
	       // 'M' instructions

`ifdef ISA_M
	       if (decoded.funct10 == f10_MULW) begin
		  let v_rd <- intMulDivRem_ALU.m_MULW (v1, v2);
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, v_rd)));
	       end

	       else if (decoded.funct10 == f10_DIVW) begin
		  let v_rd <- intMulDivRem_ALU.m_DIVW (v1, v2);
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, v_rd)));
	       end

	       else if (decoded.funct10 == f10_DIVUW) begin
		  let v_rd <- intMulDivRem_ALU.m_DIVUW (v1, v2);
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, v_rd)));
	       end

	       else if (decoded.funct10 == f10_REMW) begin
		  let v_rd <- intMulDivRem_ALU.m_REMW (v1, v2);
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, v_rd)));
	       end

	       else if (decoded.funct10 == f10_REMUW) begin
		  let v_rd <- intMulDivRem_ALU.m_REMUW (v1, v2);
		  fa_finish_normal (tagged Valid (tuple2 (decoded.rd, v_rd)));
	       end

	       else
		  fa_finish_trap (pc, exc_code_ILLEGAL_INSTRUCTION, ?);

`endif
	    endaction
	 endfunction

	 // ----------------------------------------------------------------
	 // MISC-MEM instructions
	 // Currently implemented as split-phase no-ops
	 // (todo: fix, to send/receive message from memory system?)

	 function Action fa_exec_MISC_MEM ();
	    action
	       // FENCE
	       if (   (decoded.funct3 == f3_FENCE)
		   && (decoded.rd == 0)
		   && (decoded.rs1 == 0)
		   && (instr [31:28] == 4'b0))
		  begin
		     memory.server_fence_i.request.put (?);
		     cpu_state <= STATE_EXEC_FENCE_RESPONSE;

		     if (cfg_verbosity > 1)
			$display ("RISCV_Spec.fa_exec_MISC_MEM.FENCE");
		  end

	       // FENCE.I
	       else if (   (decoded.funct3 == f3_FENCE_I)
			&& (decoded.rd == 0)
			&& (decoded.rs1 == 0)
			&& (decoded.imm12_I == 12'b0))
		  begin
		     memory.server_fence.request.put (?);
		     cpu_state <= STATE_EXEC_FENCE_I_RESPONSE;

		     if (cfg_verbosity > 1)
			$display ("RISCV_Spec.fa_exec_MISC_MEM.FENCE_I");
		  end

	       else begin
		  fa_finish_trap (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
	       end
	    endaction
	 endfunction: fa_exec_MISC_MEM

	 // ----------------------------------------------------------------
	 // System instrucions

	 function Action fa_exec_SYSTEM ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_SYSTEM");

	       // ECALL
	       if      (   (decoded.funct3 == f3_PRIV)
			&& (decoded.imm12_I == f12_ECALL)
			&& (decoded.rs1 == 0)
			&& (decoded.rd == 0))
		  begin
		     Exc_Code exc_code = (  (rg_cur_priv == u_Priv_Mode)
					  ? exc_code_ECALL_FROM_U
					  : exc_code_ECALL_FROM_M);
		     fa_finish_trap (pc, exc_code, ?);
		  end

	       // EBREAK
	       else if (   (decoded.funct3 == f3_PRIV)
			&& (decoded.imm12_I == f12_EBREAK)
			&& (decoded.rs1 == 0)
			&& (decoded.rd == 0))
		  fa_finish_trap (pc, exc_code_BREAKPOINT, ?);

	       // MRET
	       else if (   (decoded.funct3 == f3_PRIV)
			&& (rg_cur_priv == m_Priv_Mode)
			&& (decoded.imm12_I == f12_MRET)
			&& (decoded.rs1 == 0)
			&& (decoded.rd == 0))
		  begin
		     Priv_Mode from_priv = m_Priv_Mode;
		     match { .next_pc, .new_priv, .new_mstatus } <- regfiles.csr_ret_actions (from_priv);
		     rg_cur_priv <= new_priv;
		     fa_finish_cond_branch (True /* branch taken */, next_pc);
		  end

	       // WFI
	       else if (   (decoded.funct3 == f3_PRIV)
			&& (rg_cur_priv == m_Priv_Mode)
			&& (decoded.imm12_I == f12_WFI)
			&& (decoded.rs1 == 0)
			&& (decoded.rd == 0))
		  fa_finish_WFI;

	       // CSRRW
	       else if (m_v_csr matches tagged Valid .csr_old_val &&& (decoded.funct3 == f3_CSRRW)) begin
		  Word csr_new_val = v1;
		  regfiles.write_csr (decoded.csr, v1);
		  Bool wrote_instret = (decoded.csr == csr_minstret);
		  fa_finish_csrrx (tagged Valid (tuple2 (decoded.rd, csr_old_val)), wrote_instret);
	       end

	       // CSRRS
	       else if (m_v_csr matches tagged Valid .csr_old_val &&& (decoded.funct3 == f3_CSRRS)) begin
		  Bool wrote_instret = False;
		  if (decoded.rs1 != 0) begin
		     Word csr_new_val = (csr_old_val | v1);
		     regfiles.write_csr (decoded.csr, csr_new_val);
		     wrote_instret = (decoded.csr == csr_minstret);
		  end
		  fa_finish_csrrx (tagged Valid (tuple2 (decoded.rd, csr_old_val)), wrote_instret);
	       end

	       // CSRRC
	       else if (m_v_csr matches tagged Valid .csr_old_val &&& (decoded.funct3 == f3_CSRRC)) begin
		  Bool wrote_instret = False;
		  if (decoded.rs1 != 0) begin
		     Word csr_new_val = (csr_old_val & (~ v1));
		     regfiles.write_csr (decoded.csr, csr_new_val);
		     wrote_instret = (decoded.csr == csr_minstret);
		  end
		  fa_finish_csrrx (tagged Valid (tuple2 (decoded.rd, csr_old_val)), wrote_instret);
	       end

	       // CSRRWI
	       else if (m_v_csr matches tagged Valid .csr_old_val &&& (decoded.funct3 == f3_CSRRWI)) begin
		  Bool wrote_instret = (decoded.csr == csr_minstret);
		  let v1 = zeroExtend (decoded.rs1);
		  Word csr_new_val = v1;
		  regfiles.write_csr (decoded.csr, v1);
		  fa_finish_csrrx (tagged Valid (tuple2 (decoded.rd, csr_old_val)), wrote_instret);
	       end

	       // CSRRSI
	       else if (m_v_csr matches tagged Valid .csr_old_val &&& (decoded.funct3 == f3_CSRRSI)) begin
		  Bool wrote_instret = False;
		  Word v1 = zeroExtend (decoded.rs1);
		  if (v1 != 0) begin
		     Word csr_new_val = (csr_old_val | v1);
		     regfiles.write_csr (decoded.csr, csr_new_val);
		     wrote_instret = (decoded.csr == csr_minstret);
		  end
		  fa_finish_csrrx (tagged Valid (tuple2 (decoded.rd, csr_old_val)), wrote_instret);
	       end

	       // CSRRCI
	       else if (m_v_csr matches tagged Valid .csr_old_val &&& (decoded.funct3 == f3_CSRRCI)) begin
		  Bool wrote_instret = False;
		  Word v1 = zeroExtend (decoded.rs1);
		  if (v1 != 0) begin
		     Word csr_new_val = (csr_old_val & (~ v1));
		     regfiles.write_csr (decoded.csr, csr_new_val);
		     wrote_instret = (decoded.csr == csr_minstret);
		  end
		  fa_finish_csrrx (tagged Valid (tuple2 (decoded.rd, csr_old_val)), wrote_instret);
	       end

	       else begin
		  fa_finish_trap (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
	       end
	    endaction
	 endfunction: fa_exec_SYSTEM

	 // ----------------------------------------------------------------
	 // Main body of fa_exec(), dispatching to the sub functions
	 // based on major OPCODE

	 if (cfg_verbosity != 0)
	    $display ("RISCV_Spec.fa_exec: instr 0x%0h", instr);

	 if      (decoded.opcode == op_LUI)       fa_exec_LUI;
	 else if (decoded.opcode == op_AUIPC)     fa_exec_AUIPC;
	 else if (decoded.opcode == op_JAL)       fa_exec_JAL;
	 else if (decoded.opcode == op_JALR)      fa_exec_JALR;
	 else if (decoded.opcode == op_BRANCH)    fa_exec_BRANCH;
	 else if (decoded.opcode == op_LOAD)      fa_exec_LD_req;
	 else if (decoded.opcode == op_STORE)     fa_exec_ST_req;
	 else if (decoded.opcode == op_OP_IMM)    fa_exec_OP_IMM;
	 else if (decoded.opcode == op_OP)        fa_exec_OP;
	 else if (decoded.opcode == op_MISC_MEM)  fa_exec_MISC_MEM;
	 else if (decoded.opcode == op_SYSTEM)    fa_exec_SYSTEM;

	 // 32b ops in RV64 only
	 else if ((decoded.opcode == op_OP_IMM_32) && (xlen == 64)) fa_exec_OP_IMM_32;
	 else if ((decoded.opcode == op_OP_32)     && (xlen == 64)) fa_exec_OP_32;

	 else fa_finish_trap (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
      endaction
   endfunction: fa_exec

   // ================================================================
   // The CPU's top-level state machine

   // ---------------- FETCH
   // Issue instruction request
   // (provided there is no interrupt or gdb-stop pending)

   rule rl_fetch (cpu_state == STATE_FETCH);
      // Take gdb-stop request, if present
      if (rg_gdb_stop_req) begin
	 if (cfg_verbosity > 1)
	    $display ("%0d: RISCV_Spec.rl_fetch: Stopping for GDB", cur_cycle);

	 rg_gdb_stop_req <= False;
	 cpu_state <= STATE_IDLE;
      end

      // Take external interrupt, if present
      else if (rg_interrupt_req matches tagged Valid .exc_code) begin
	 if (cfg_verbosity > 1)
	    $display ("%0d: RISCV_Spec.rl_fetch: Taking external interrupt w. exc_code %0d; PC is 0x%08h",
		      cur_cycle, exc_code, pc);
	 rg_interrupt_req <= tagged Invalid;    // consume the request
	 fa_finish_interrupt (pc, exc_code);
      end

      // Normal instruction fetch
      else begin
	 if (cfg_verbosity > 1)
	    $display ("%0d: RISCV_Spec.rl_fetch: Fetching at PC 0x%0h", cur_cycle, pc);

	 memory.imem_req (pc);
	 cpu_state <= STATE_EXEC;

	 // If stepping, raise gdb stop request
	 if (rg_gdb_step_req) begin
	    rg_gdb_stop_req <= True;
	    rg_gdb_step_req <= False;
	 end
      end
   endrule

   // ---------------- EXECUTE
   // Receive instruction from IMem; handle exception if any, else execute it;
   // for LD/ST, issue request and move to LD_RESPONSE/ST_RESPONSE state)

   rule rl_exec (cpu_state == STATE_EXEC);
      if (cfg_verbosity > 1)
	 $display ("%0d: RISCV_Spec.rl_exec", cur_cycle);

      let imem_resp <- memory.imem_resp;

      case (imem_resp) matches
	 // IMem response is an exception
	 tagged IMem_Resp_Exception .exc_code:
	    begin
	       fa_finish_trap (pc, exc_code, pc);
	    end

	 // IMem response is ok
	 tagged IMem_Resp_Ok  .instr:
	    begin
	       rg_instr <= instr;
	       fa_exec (instr);
	    end
      endcase
   endrule

   // ---------------- LD-responses from DMem

   rule rl_exec_LD_response (cpu_state == STATE_EXEC_LD_RESPONSE);
      if (cfg_verbosity > 1)
	 $display ("%0d: RISCV_Spec.rl_exec_LD_response", cur_cycle);

      Decoded_Instr decoded = fv_decode (rg_instr);

      let resp <- memory.dmem_resp;

      case (resp) matches
	 tagged DMem_Resp_Exception .exc_code: fa_finish_trap (pc, exc_code, rg_mem_addr);
	 tagged DMem_Resp_Ok .u:
	    begin
	       Word value = ?;
	       case (decoded.funct3)
		  f3_LB:  begin
			     Int #(8) s8    = unpack (truncate (u));
			     Word_S   s     = signExtend (s8);
			     value = pack (s);
			  end
		  f3_LBU: begin
			     Bit #(8) u8    = truncate (u);
			     value = zeroExtend (u8);
			  end
		  f3_LH:  begin
			     Int #(16) s16   = unpack (truncate (u));
			     Word_S    s     = signExtend (s16);
			     value = pack (s);
			  end
		  f3_LHU: begin
			     Bit #(16) u16   = truncate (u);
			     value = zeroExtend (u16);
			  end
		  f3_LW:  begin
			     Int #(32) s32   = unpack (truncate (u));
			     Word_S    s     = signExtend (s32);
			     value = pack (s);
			  end
		  f3_LWU: begin  // Note: request has already checked that LWU is legal (i.e., RV64 only)
			     Bit #(32) u32   = truncate (u);
			     value = zeroExtend (u32);
			  end
		  f3_LD:  begin  // Note: request has already checked that LD is legal (i.e., RV64 only)
			     value = u;
			  end
		  // Note: request has already checked that 'default' case is impossible
	       endcase
	       fa_finish_normal (tagged Valid (tuple2 (decoded.rd, value)));
	    end
      endcase
   endrule

   // ---------------- ST-responses from DMem

   rule rl_exec_ST_response (cpu_state == STATE_EXEC_ST_RESPONSE);
      if (cfg_verbosity > 1)
	 $display ("%0d: RISCV_Spec.rl_exec_ST_response", cur_cycle);

      DMem_Resp resp <- memory.dmem_resp;

      case (resp) matches
	 tagged DMem_Resp_Exception .exc_code: fa_finish_trap (pc, exc_code, rg_mem_addr);
	 tagged DMem_Resp_Ok        .u:        fa_finish_normal (tagged Invalid);
      endcase
   endrule

   // ---------------- FENCE_I-responses from DMem

   rule rl_exec_FENCE_I_response (cpu_state == STATE_EXEC_FENCE_I_RESPONSE);
      // Await mem system FENCE.I completion
      let dummy <- memory.server_fence_i.response.get;

      if (cfg_verbosity > 1)
	 $display ("%0d: RISCV_Spec.rl_exec_FENCE_I_response", cur_cycle);

      fa_finish_normal (tagged Invalid);
   endrule

   // ---------------- FENCE-responses from DMem

   rule rl_exec_FENCE_response (cpu_state == STATE_EXEC_FENCE_RESPONSE);
      // Await mem system FENCE completion
      let dummy <- memory.server_fence.response.get;

      if (cfg_verbosity > 1)
	 $display ("%0d: RISCV_Spec.rl_exec_FENCE_response", cur_cycle);

      fa_finish_normal (tagged Invalid);
   endrule

   // ---------------- WFI

   rule rl_exec_WFI (cpu_state == STATE_WFI);
      if (cfg_verbosity > 1)
	 $display ("%0d: RISCV_Spec.rl_exec_WFI", cur_cycle);
   endrule

   // ----------------------------------------------------------------
   // INTERFACE

   // ----------------
   // Reset

   method Action reset;
      pc           <= pc_reset_value;
      rg_cur_priv  <= m_Priv_Mode;

      rg_gdb_stop_req <= False;
      rg_interrupt_req <= tagged Invalid;
   endmethod

   // ----------------
   // Run control

   method Action start;
      cpu_state       <= STATE_FETCH;
      rg_gdb_step_req <= False;
   endmethod

   method Action step;
      cpu_state       <= STATE_FETCH;
      rg_gdb_step_req <= True;
   endmethod

   method Bool stopped;
      return (cpu_state == STATE_IDLE);
   endmethod

   method Action gdb_stop_req;
      rg_gdb_stop_req <= True;
   endmethod

   // ----------------
   // Continuous signal from external interrupt controller
   //   tagged Invalid    => no interrupt pending
   //   tagged Valid ec   => interrupt pending with ec exception code

   method Action interrupt_req (Maybe #(Exc_Code) m_exc_code);
      rg_interrupt_req <= m_exc_code;
   endmethod

   // ----------------
   // Non-deterministic external request to increment "CYCLE" counter

   method Action incr_cycle;
      regfiles.csr_mcycle_incr;
   endmethod

   // ----------------
   // Debugger access to architectural state

   method Word   read_gpr  (RegName r);
      return ((r == 0) ? 0 : regfiles.read_rs1_port2 (r));
   endmethod

   method Action write_gpr (RegName r, Word value);
      if (r != 0)
	 regfiles.write_rd (r, value);
   endmethod

   method Word   read_pc;
      return pc;
   endmethod

   method Action write_pc  (Addr pc_value);
      pc <= pc_value;
   endmethod

   method Maybe #(Word) read_csr  (CSR_Addr csr_addr);
      return regfiles.read_csr (csr_addr);
   endmethod

   method Action write_csr (CSR_Addr csr_addr, Word csr_value);
      regfiles.write_csr (csr_addr, csr_value);
   endmethod
endmodule  

// ================================================================

endpackage
