// Copyright (c) 2016 Bluespec, Inc.  All Rights Reserved.
// Author: Rishiyur S. Nikhil

// This is a formal specification of the RISC-V ISA, given as an
// executable BSV module representing a RISC-V CPU.
// The module's parameters are:
//  - an interface to memory,
//  - booleans from an external oracle indicating when to
//        increment its cycle and time counters.

// Although one could write the entire instruction fetch-execute loop
// in BSV as a single rule (hence a single atomic Action), we
// deliberately break it at Instruction and Data memory accesses,
// i.e., issuing a request to memory and receiving a response are two
// separate actions.  This allows plugging this spec into contexts
// with concurrency and non-determinism, i.e., allowing interleavings
// with other actions (in the environment outside the CPU) during the
// memory access (MMU page table walks, caching, multiprocessors, ...)
// that may have non-deterministic and concurrent executions of

// This code is executable (and has been executed on numerous
// RISC-VELF binaries).  Usually one executes it in Bluesim,
// Bluespec's BSV simulator.  However, it can also be compiled into
// synthesizable Verilog, which can be executed in a Verilog simulator
// or on an FPGA.

package RISCV_Spec;

// ================================================================
// BSV library imports

import RegFile   :: *;    // For RISC-V GPRs

// ================================================================
// BSV project imports

import ISA_Decls :: *;    // Instruction encodings

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
// and is used insided the module to access memory.
// MMUs, caches etc. are outside this boundary.

interface Memory_IFC;
   method Action                   imem_req (Addr addr);
   method ActionValue #(IMem_Resp) imem_resp;

   method Action                   dmem_req (DMem_Req req);
   method ActionValue #(DMem_Resp) dmem_resp;
endinterface

// ================================================================
// This interfacce is offered by the 'mkRISCV_Spec' module to the environment.
// It is not part of the spec, per se, and just has scaffolding that allows
// the environment to control and CPU and probe its state.

interface RISCV_Spec_IFC;
   method Action start (Addr initial_pc);
   method Bool   stopped;

   method Word   read_gpr  (RegName r);
   method Action write_gpr (RegName r, Word value);

   method Word   read_pc;
   method Action write_pc  (Addr pc_value);

   method Word   read_csr  (CSR_Addr csr_addr);
   method Action write_csr (CSR_Addr csr_addr, Word csr_value);
endinterface

// ================================================================
// The RISC-V CPU Specification module, 'mkRISCV_Spec'

// ----------------
// The CPU is initially in the IDLE state.
// It starts running when it is put into the FETCH state.
// When running, it cycles through the following sequences of states:
//
//     FETCH -> EXEC ->                     FINISH    for most instructions
//     FETCH -> EXEC -> EXEC_LD_RESPONSE -> FINISH    for LD instructions
//     FETCH -> EXEC -> EXEC_ST_RESPONSE -> FINISH    for ST instructions
//
// From any of the FETCH/EXEC states, an exception takes it to the ENV_CALL state
// and execution stops (this is for user-mode instructions, covered here;
// when we extend to machine-mode etc., ENV_CALL will vector through
// a trap handler and execution will continue there).
//
// In general, after any of the EXEC states, we could immediately return
// to FETCH (assuming no exception). The only purpose of FINISH is to
// resolve what happens to CSR_INSTRET when the current instruction is
// a CSRRx instruction that updates CSR_INSTRET.  In this one case, we do
// not increment CSR_INSTRET, otherwise it is incremented.  This information
// is passed in the flag 'csr_instret_written'.  We could remove this FINISH
// state and fold in the conditional increment of CSR_INSTRET into other
// finish-actions, but that would add significant clutter to the code.

typedef enum {STATE_IDLE,
	      STATE_FETCH,
	      STATE_EXEC,
	      STATE_EXEC_LD_RESPONSE,
	      STATE_EXEC_ST_RESPONSE,
	      STATE_FINISH,
	      STATE_ENV_CALL
   } CPU_STATE
deriving (Eq, Bits, FShow);

// ----------------
// Default fall-through PC

function Addr fv_fall_through_pc (Addr pc);
   return pc + 4;
endfunction: fv_fall_through_pc

// ----------------

module mkRISCV_Spec #(Memory_IFC  memory,            // interface to instr and data memories
		      Bool        incr_cycle,        // when to increment CSR_CYCLE 
		      Bool        incr_time,         // when to increment CSR_TIME
		      Bit #(4)    cfg_verbosity)     // of info messages during execution
   (RISCV_Spec_IFC);

   // Program counter
   Reg #(Word) pc <- mkRegU;

   // General Purpose Registers
   RegFile #(RegName, Word) regfile <- mkRegFileFull;

   // CSRs
   Reg #(Bit #(64)) csr_cycle   <- mkRegU;
   Reg #(Bit #(64)) csr_time    <- mkRegU;
   Reg #(Bit #(64)) csr_instret <- mkRegU;

   Reg #(Bool)      csr_instret_written <- mkReg (False);    // Is csr_instret updated by this instr?

   // ----------------
   // These CSRs are technically not present in the user-mode ISA.
   // We have them here so that we can at least record the cause, so that the
   // environment (Supervisor, Hypervisor, Machine, or magic) can deal with it.
   // They will actually be used when we extend the spec to include machine-mode.

   Reg #(Word) csr_mepc     <- mkRegU;
   Reg #(Word) csr_mcause   <- mkRegU;
   Reg #(Word) csr_mbadaddr <- mkRegU;

   // ----------------
   // These CSRs are technically not present in the user-mode ISA.
   // We have them here because even bare-metal riscv-gcc ELF binaries access them.

   Reg #(Word) csr_mstatus  <- mkRegU;
   Reg #(Word) csr_mtvec    <- mkRegU;

   // ----------------------------------------------------------------
   // Non-architectural state, for this model

   Reg #(CPU_STATE) cpu_state   <- mkReg (STATE_IDLE);
   Reg #(Addr)      rg_mem_addr <- mkRegU;    // Effective addr in LD/ST
   Reg #(Word)      rg_instr    <- mkRegU;    // Current instruction

   // ----------------------------------------------------------------
   // Read a CSR
   // If the addr is valid, return tagged Valid value
   // else return tagged Invalid

   function Maybe #(Word) fv_read_csr (CSR_Addr csr_addr);
      if      (csr_addr == csr_CYCLE)    return tagged Valid truncate    (csr_cycle);
      else if (csr_addr == csr_TIME)     return tagged Valid truncate    (csr_time);
      else if (csr_addr == csr_INSTRET)  return tagged Valid truncate    (csr_instret);

      else if ((csr_addr == csr_CYCLEH)   && (xlen == 32))  return tagged Valid truncateLSB (csr_cycle);
      else if ((csr_addr == csr_TIMEH)    && (xlen == 32))  return tagged Valid truncateLSB (csr_time);
      else if ((csr_addr == csr_INSTRETH) && (xlen == 32))  return tagged Valid truncateLSB (csr_instret);

      else if (csr_addr == csr_MSTATUS)  return tagged Valid csr_mstatus;
      else if (csr_addr == csr_MTVEC)    return tagged Valid csr_mtvec;

      else return tagged Invalid;
   endfunction: fv_read_csr

   // ----------------------------------------------------------------
   // Write a CSR
   // We assume a valid csr_addr, since this is always preceded by a read_csr which performs the check

   function Action fa_write_csr (CSR_Addr csr_addr, Word csr_value);
      action
	 if      (csr_addr == csr_MSTATUS)  csr_mstatus <= zeroExtend (csr_value);
	 else if (csr_addr == csr_MTVEC)    csr_mtvec   <= zeroExtend (csr_value);

	 else if (csr_addr == csr_CYCLE)    csr_cycle   <= zeroExtend (csr_value);
	 else if (csr_addr == csr_TIME)     csr_time    <= zeroExtend (csr_value);
	 else if (csr_addr == csr_INSTRET) begin
	    csr_instret         <= zeroExtend (csr_value);
	    csr_instret_written <= True;
	 end

	 else if ((csr_addr == csr_CYCLEH)   && (xlen == 32))
	    csr_cycle <= { csr_value [31:0], truncate (csr_cycle) };

	 else if ((csr_addr == csr_TIMEH)    && (xlen == 32))
	    csr_time  <= { csr_value [31:0], truncate (csr_time) };

	 else if ((csr_addr == csr_INSTRETH) && (xlen == 32)) begin
	    csr_instret         <= { csr_value [31:0], truncate (csr_instret) };
	    csr_instret_written <= True;
	 end

	 else begin
	    $display ("ERROR: RISCV_Spec.fa_write_csr (csr_addr 0x%0h, csr_value 0x%0h): illegal csr_addr",
		      csr_addr, csr_value);
	 end
      endaction
   endfunction: fa_write_csr

   // ================================================================
   // Instruction execution

   // ----------------------------------------------------------------
   // The following functions are common idioms for finishing an instruction

   // ----------------
   // Finish exception: record exception cause info, go to ENV_CALL state

   function Action fa_finish_with_exception (Word epc, Exc_Code exc_code, Addr badaddr);
      action
	 if ((cfg_verbosity != 0) || (exc_code == exc_code_ILLEGAL_INSTRUCTION))
	    $display ("RISCV_Spec.fa_do_exception: epc = 0x%0h, exc_code = 0x%0h, badaddr = 0x%0h",
		      epc, exc_code, badaddr);

	 csr_mepc     <= epc;
	 csr_mcause   <= { 1'b0, 0, exc_code };
	 csr_mbadaddr <= badaddr;

	 cpu_state   <= STATE_ENV_CALL;
      endaction
   endfunction

   // ----------------
   // Finish instr with no output (no Rd-write): set PC, go to FETCH state

   function Action fa_finish_with_no_output ();
      action
	 if (cfg_verbosity > 1)
	    $display ("RISCV_Spec.fa_finish_with_no_output");

	 pc <= fv_fall_through_pc (pc);
	 cpu_state <= STATE_FINISH;
      endaction
   endfunction

   // ----------------
   // Finish instr with Rd-write: write Rd, set PC, go to FETCH state

   function Action fa_finish_with_Rd (RegName rd, Word rd_value);
      action
	 if (cfg_verbosity > 1)
	    $display ("RISCV_Spec.fa_finish_with_Rd: Rd 0x%0h, value 0x%0h", rd, rd_value);

	 if (rd != 0) regfile.upd (rd, rd_value);
	 pc <= fv_fall_through_pc (pc);
	 cpu_state <= STATE_FINISH;
      endaction
   endfunction

   // ----------------
   // Finish jump instrs; write Rd, set PC, go to FETCH state

   function Action fa_finish_jump (RegName rd, Word rd_value, Addr next_pc);
      action
	 if (cfg_verbosity > 1)
	    $display ("RISCV_Spec.fa_finish_jump: Rd 0x%0h, value 0x%0h, next_pc 0x%0h",
		      rd, rd_value, next_pc);

	 if (rd != 0) regfile.upd (rd, rd_value);
	 pc <= next_pc;
	 cpu_state <= STATE_FINISH;
      endaction
   endfunction

   // ----------------
   // Finish conditional branch instr: set PC, go to FETCH state

   function Action fa_finish_cond_branch (Bool branch_taken, Addr next_pc);
      action
	 if (cfg_verbosity > 1)
	    $display ("RISCV_Spec.fa_finish_cond_branch: Taken %0d, pc 0x%0h, next_pc 0x%0h",
		      pack (branch_taken), pc, next_pc);

	 pc <= (branch_taken ? next_pc : fv_fall_through_pc (pc));
	 cpu_state <= STATE_FINISH;
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
	 Word    v1   = ((decoded.rs1 == 0) ? 0: regfile.sub (decoded.rs1));
	 Word    v2   = ((decoded.rs2 == 0) ? 0: regfile.sub (decoded.rs2));

	 // Values of Rs1 and Rs2 fields of the instr, signed versions
	 Word_S  s_v1 = unpack (v1);
	 Word_S  s_v2 = unpack (v2);

	 // 32b versions of the above, For 32b instrs in RV64I
	 Bit #(32)  v1_32   = truncate (v1);
	 Bit #(32)  v2_32   = truncate (v2);
	 Int #(32)  s_v1_32 = unpack (v1_32);
	 Int #(32)  s_v2_32 = unpack (v2_32);

	 // Value of CSR field of instr (if a valid CSR address)
	 Maybe #(Word) m_v_csr = fv_read_csr (decoded.csr);

	 // ----------------------------------------------------------------
	 // Instructions for Upper Immediate

	 function Action fa_exec_LUI ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_LUI");

	       Bit #(32)  v32   = { decoded.imm20_U, 12'h0 };
	       Word_S     iv    = extend (unpack (v32));
	       let        value = pack (iv);

	       fa_finish_with_Rd (decoded.rd, value);
	    endaction
	 endfunction: fa_exec_LUI

	 function Action fa_exec_AUIPC ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_AUIPC");

	       Word_S  iv    = extend (unpack ({ decoded.imm20_U, 12'b0}));
	       Word_S  pc_s  = unpack (pc);
	       Word    value = pack (pc_s + iv);

	       fa_finish_with_Rd (decoded.rd, value);
	    endaction
	 endfunction: fa_exec_AUIPC

	 // ----------------------------------------------------------------
	 // Instructions for control-transfer

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
	       else fa_finish_with_exception (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
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
	       else fa_finish_with_exception (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
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
	       else fa_finish_with_exception (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
	    endaction
	 endfunction: fa_exec_ST_req

	 // ----------------------------------------------------------------
	 // Instructios for Register-Immediate alu ops

	 function Action fa_exec_OP_IMM ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_OP_IMM");

	       Word                v2    = zeroExtend (decoded.imm12_I);
	       Word_S              s_v2  = signExtend (unpack (decoded.imm12_I));
	       Bit #(TLog #(XLEN)) shamt = truncate (decoded.imm12_I);

	       if      (decoded.funct3 == f3_ADDI)  fa_finish_with_Rd (decoded.rd, pack (s_v1 + s_v2));
	       else if (decoded.funct3 == f3_SLTI)  fa_finish_with_Rd (decoded.rd, ((s_v1 < s_v2) ? 1 : 0));
	       else if (decoded.funct3 == f3_SLTIU) fa_finish_with_Rd (decoded.rd, ((v1  < v2)  ? 1 : 0));
	       else if (decoded.funct3 == f3_XORI)  fa_finish_with_Rd (decoded.rd, pack (s_v1 ^ s_v2));
	       else if (decoded.funct3 == f3_ORI)   fa_finish_with_Rd (decoded.rd, pack (s_v1 | s_v2));
	       else if (decoded.funct3 == f3_ANDI)  fa_finish_with_Rd (decoded.rd, pack (s_v1 & s_v2));

	       else if (   (decoded.funct3 == f3_SLLI)
			&& (   ((xlen == 32) && (instr [31:25] == 7'b000_0000))
			    || ((xlen == 64) && (instr [31:26] == 6'b000_000 ))))
		  fa_finish_with_Rd (decoded.rd, (v1 << shamt));


	       // SRLI
	       else if (   (decoded.funct3 == f3_SRxI)
			&& (   ((xlen == 32) && (instr [31:25] == 7'b000_0000))
			    || ((xlen == 64) && (instr [31:26] == 6'b000_000 ))))
		  fa_finish_with_Rd (decoded.rd, (v1 >> shamt));

	       // SRAI
	       else if (   (decoded.funct3 == f3_SRxI)
			&& (   ((xlen == 32) && (instr [31:25] == 7'b010_0000))
			    || ((xlen == 64) && (instr [31:26] == 6'b010_000 ))))
		  fa_finish_with_Rd (decoded.rd, pack (s_v1 >> shamt));

	       // ---- 32b instrs in RV64I

	       else if (   (decoded.funct3 == f3_ADDIW)
			&& (xlen == 64))
                  begin
		     Int #(32) s_v2_32 = signExtend (unpack (decoded.imm12_I));
		     fa_finish_with_Rd (decoded.rd, pack (signExtend ((s_v1_32 + s_v2_32))));
		  end

	       else if (   (decoded.funct3 == f3_SLLIW)
			&& (xlen == 64)
			&& (instr [31:25] == 7'b000_0000))
		  fa_finish_with_Rd (decoded.rd, signExtend (v1_32 << shamt));

	       // SRLIW
	       else if (   (decoded.funct3 == f3_SRxIW)
			&& (xlen == 64)
			&& (instr [31:25] == 7'b000_0000))
		  fa_finish_with_Rd (decoded.rd, signExtend (v1_32 >> shamt));

	       // SRAIW
	       else if (   (decoded.funct3 == f3_SRxIW)
			&& (xlen == 64)
			&& (instr [31:25] == 7'b010_0000))
		  fa_finish_with_Rd (decoded.rd, signExtend (pack (s_v1_32 >> shamt)));

	       else 
		  fa_finish_with_exception (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
	    endaction
	 endfunction: fa_exec_OP_IMM

	 // ----------------------------------------------------------------
	 // Instructios for Register-Register alu ops

	 function Action fa_exec_OP ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_OP");

	       Bit #(TLog #(XLEN)) shamt = truncate (v2);    // Caveat: upper bits are unspecified, per spec doc

	       if      (decoded.funct10 == f10_ADD)  fa_finish_with_Rd (decoded.rd, pack (s_v1 + s_v2));
	       else if (decoded.funct10 == f10_SUB)  fa_finish_with_Rd (decoded.rd, pack (s_v1 - s_v2));
	       else if (decoded.funct10 == f10_SLL)  fa_finish_with_Rd (decoded.rd, (v1 << shamt));
	       else if (decoded.funct10 == f10_SLT)  fa_finish_with_Rd (decoded.rd, ((s_v1 < s_v2) ? 1 : 0));
	       else if (decoded.funct10 == f10_SLTU) fa_finish_with_Rd (decoded.rd, ((v1  < v2)  ? 1 : 0));
	       else if (decoded.funct10 == f10_XOR)  fa_finish_with_Rd (decoded.rd, pack (s_v1 ^ s_v2));
	       else if (decoded.funct10 == f10_SRL)  fa_finish_with_Rd (decoded.rd, (v1 >> shamt));
	       else if (decoded.funct10 == f10_SRA)  fa_finish_with_Rd (decoded.rd, pack (s_v1 >> shamt));
	       else if (decoded.funct10 == f10_OR)   fa_finish_with_Rd (decoded.rd, pack (s_v1 | s_v2));
	       else if (decoded.funct10 == f10_AND)  fa_finish_with_Rd (decoded.rd, pack (s_v1 & s_v2));

	       // ---- 32b instrs in RV64I

	       else if ((decoded.funct10 == f10_ADDW) && (xlen == 64))
		  fa_finish_with_Rd (decoded.rd, pack (signExtend (s_v1_32 + s_v2_32)));

	       else if ((decoded.funct10 == f10_SUBW) && (xlen == 64))
		  fa_finish_with_Rd (decoded.rd, pack (signExtend (s_v1_32 - s_v2_32)));

	       else if ((decoded.funct10 == f10_SLLW) && (xlen == 64))
		  fa_finish_with_Rd (decoded.rd, pack (signExtend (v1_32 << shamt)));

	       else if ((decoded.funct10 == f10_SRLW) && (xlen == 64))
		  fa_finish_with_Rd (decoded.rd, pack (signExtend (v1_32 >> shamt)));

	       else if ((decoded.funct10 == f10_SRAW) && (xlen == 64))
		  fa_finish_with_Rd (decoded.rd, pack (signExtend (s_v1_32 >> shamt)));

	       else
		  fa_finish_with_exception (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
	    endaction
	 endfunction: fa_exec_OP

	 // ----------------------------------------------------------------
	 // Instructions for MISC-MEM
	 // Currently implemented as no-ops (todo: fix)

	 function Action fa_exec_MISC_MEM ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_MISC_MEM");

	       // FENCE
	       if (   (decoded.funct3 == f3_FENCE)
		   && (decoded.rd == 0)
		   && (decoded.rs1 == 0)
		   && (instr [31:28] == 4'b0)) begin
						  fa_finish_with_no_output;
					       end

	       // FENCE.I
	       else if (   (decoded.funct3 == f3_FENCE_I)
			&& (decoded.rd == 0)
			&& (decoded.rs1 == 0)
			&& (decoded.imm12_I == 12'b0)) begin
							  fa_finish_with_no_output;
						       end

	       else begin
		  fa_finish_with_exception (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
	       end
	    endaction
	 endfunction: fa_exec_MISC_MEM

	 // ----------------------------------------------------------------
	 // Instrucions for System-level ops

	 function Action fa_exec_SYSTEM ();
	    action
	       if (cfg_verbosity > 1)
		  $display ("RISCV_Spec.fa_exec_SYSTEM");

	       // SCALL/ECALL
	       if      (   (decoded.funct3 == f3_PRIV)
			&& (decoded.imm12_I == f12_ECALL)
			&& (decoded.rs1 == 0)
			&& (decoded.rd == 0))
		  fa_finish_with_exception (pc, exc_code_ECALL_FROM_U, ?);

	       // SBREAK/EBREAK
	       else if (   (decoded.funct3 == f3_PRIV)
			&& (decoded.imm12_I == f12_EBREAK)
			&& (decoded.rs1 == 0)
			&& (decoded.rd == 0))
		  fa_finish_with_exception (pc, exc_code_BREAKPOINT, ?);

	       // CSRRW
	       else if (m_v_csr matches tagged Valid .csr_old_val &&& (decoded.funct3 == f3_CSRRW)) begin
		  fa_write_csr (decoded.csr, v1);
		  fa_finish_with_Rd (decoded.rd, csr_old_val);
	       end

	       // CSRRS
	       else if (m_v_csr matches tagged Valid .csr_old_val &&& (decoded.funct3 == f3_CSRRS)) begin
		  if (decoded.rs1 != 0) begin
		     Word csr_new_val = (csr_old_val | v1);
		     fa_write_csr (decoded.csr, csr_new_val);
		  end
		  fa_finish_with_Rd (decoded.rd, csr_old_val);
	       end

	       // CSRRC
	       else if (m_v_csr matches tagged Valid .csr_old_val &&& (decoded.funct3 == f3_CSRRC)) begin
		  if (decoded.rs1 != 0) begin
		     Word csr_new_val = (csr_old_val & (~ v1));
		     fa_write_csr (decoded.csr, csr_new_val);
		  end
		  fa_finish_with_Rd (decoded.rd, csr_old_val);
	       end

	       // CSRRWI
	       else if (m_v_csr matches tagged Valid .csr_old_val &&& (decoded.funct3 == f3_CSRRW)) begin
		  let v1 = zeroExtend (decoded.rs1);
		  fa_write_csr (decoded.csr, v1);
		  fa_finish_with_Rd (decoded.rd, csr_old_val);
	       end

	       // CSRRSI
	       else if (m_v_csr matches tagged Valid .csr_old_val &&& (decoded.funct3 == f3_CSRRS)) begin
		  Word v1 = zeroExtend (decoded.rs1);
		  if (v1 != 0) begin
		     Word csr_new_val = (csr_old_val | v1);
		     fa_write_csr (decoded.csr, csr_new_val);
		  end
		  fa_finish_with_Rd (decoded.rd, csr_old_val);
	       end

	       // CSRRCI
	       else if (m_v_csr matches tagged Valid .csr_old_val &&& (decoded.funct3 == f3_CSRRC)) begin
		  Word v1 = zeroExtend (decoded.rs1);
		  if (v1 != 0) begin
		     Word csr_new_val = (csr_old_val & (~ v1));
		     fa_write_csr (decoded.csr, csr_new_val);
		  end
		  fa_finish_with_Rd (decoded.rd, csr_old_val);
	       end

	       else begin
		  fa_finish_with_exception (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
	       end
	    endaction
	 endfunction: fa_exec_SYSTEM

	 // ----------------------------------------------------------------
	 // Main body of fa_exec(), dispatching to the sub functions
	 // based on major OPCODE

	 if (cfg_verbosity != 0)
	    $display ("RISCV_Spec.fa_exec: instr 0x%0h", instr);

	 if      (decoded.opcode == op_LUI)      fa_exec_LUI;
	 else if (decoded.opcode == op_AUIPC)    fa_exec_AUIPC;
	 else if (decoded.opcode == op_JAL)      fa_exec_JAL;
	 else if (decoded.opcode == op_JALR)     fa_exec_JALR;
	 else if (decoded.opcode == op_BRANCH)   fa_exec_BRANCH;
	 else if (decoded.opcode == op_LOAD)     fa_exec_LD_req;
	 else if (decoded.opcode == op_STORE)    fa_exec_ST_req;
	 else if (decoded.opcode == op_OP_IMM)   fa_exec_OP_IMM;
	 else if (decoded.opcode == op_OP)       fa_exec_OP;
	 else if (decoded.opcode == op_MISC_MEM) fa_exec_MISC_MEM;
	 else if (decoded.opcode == op_SYSTEM)   fa_exec_SYSTEM;
	 else fa_finish_with_exception (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
      endaction
   endfunction: fa_exec

   // ================================================================
   // The CPU's top-level state machine

   // ---------------- FETCH
   // Issue instruction request

   rule rl_fetch (cpu_state == STATE_FETCH);
      if (cfg_verbosity > 1)
	 $display ("RISCV_Spec.rl_fetch: STATE_FETCH");

      memory.imem_req (pc);
      csr_instret_written <= False;
      cpu_state <= STATE_EXEC;
   endrule

   // ---------------- EXECUTE
   // Receive instruction from IMem; handle exception if any, else execute it;
   // for LD/ST, issue request and move to LD_RESPONSE/ST_RESPONSE state)

   rule rl_exec (cpu_state == STATE_EXEC);
      if (cfg_verbosity > 1)
	 $display ("RISCV_Spec.rl_exec: STATE_EXEC");

      let imem_resp <- memory.imem_resp;

      case (imem_resp) matches
	 // IMem response is an exception
	 tagged IMem_Resp_Exception .exc_code:
	    begin
	       fa_finish_with_exception (pc, exc_code, pc);
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
	 $display ("RISCV_Spec.rl_exec_LD_response: STATE_EXEC_LD_RESPONSE");

      Decoded_Instr decoded = fv_decode (rg_instr);

      let resp <- memory.dmem_resp;

      case (resp) matches
	 tagged DMem_Resp_Exception .exc_code: fa_finish_with_exception (pc, exc_code, rg_mem_addr);
	 tagged DMem_Resp_Ok .u:
	    case (decoded.funct3)
	       f3_LB:  begin
			  Int #(8) s8    = unpack (truncate (u));
			  Word_S   s     = signExtend (s8);
			  Word     value = pack (s);
			  fa_finish_with_Rd (decoded.rd, value);
		       end
	       f3_LBU: begin
			  Bit #(8) u8    = truncate (u);
			  Word     value = zeroExtend (u8);
			  fa_finish_with_Rd (decoded.rd, value);
		       end
	       f3_LH:  begin
			  Int #(16) s16   = unpack (truncate (u));
			  Word_S    s     = signExtend (s16);
			  Word      value = pack (s);
			  fa_finish_with_Rd (decoded.rd, value);
		       end
	       f3_LHU: begin
			  Bit #(16) u16   = truncate (u);
			  Word      value = zeroExtend (u16);
			  fa_finish_with_Rd (decoded.rd, value);
		       end
	       f3_LW:  begin
			  Int #(32) s32   = unpack (truncate (u));
			  Word_S    s     = signExtend (s32);
			  Word      value = pack (s);
			  fa_finish_with_Rd (decoded.rd, value);
		       end
	       f3_LWU: begin    // Note: request has already checked that LWU is legal (i.e., RV64 only)
			  Bit #(32) u32   = truncate (u);
			  Word      value = zeroExtend (u32);
			  fa_finish_with_Rd (decoded.rd, value);
		       end
	       f3_LD:  begin    // Note: request has already checked that LD is legal (i.e., RV64 only)
			  Word value = u;
			  fa_finish_with_Rd (decoded.rd, value);
		       end
	       // Note: request has already checked that 'default' case is impossible
	    endcase
      endcase
   endrule

   // ---------------- ST-responses from DMem

   rule rl_exec_ST_response (cpu_state == STATE_EXEC_ST_RESPONSE);
      if (cfg_verbosity > 1)
	 $display ("RISCV_Spec.rl_exec_ST_response: STATE_EXEC_ST_RESPONSE");

      DMem_Resp resp <- memory.dmem_resp;

      case (resp) matches
	 tagged DMem_Resp_Exception .exc_code: fa_finish_with_exception (pc, exc_code, rg_mem_addr);
	 tagged DMem_Resp_Ok        .u:        fa_finish_with_no_output;
      endcase
   endrule

   // ---------------- FINISH: increment csr_instret or record explicit CSRRx update of csr_instret

   rule rl_finish (cpu_state == STATE_FINISH);
      if (! csr_instret_written)
	 csr_instret <= csr_instret + 1;
      cpu_state <= STATE_FETCH;
   endrule

   // ---------------- Increment csr_cycle and csr_time according to external oracles

   rule rl_incr_cycle (incr_cycle);
      csr_cycle <= csr_cycle + 1;
   endrule

   rule rl_incr_time (incr_time);
      csr_time <= csr_time + 1;
   endrule

   // ----------------------------------------------------------------
   // INTERFACE

   method Action start (Addr initial_pc);
      pc        <= initial_pc;
      cpu_state <= STATE_FETCH;
   endmethod

   method Bool stopped;
      return (cpu_state == STATE_ENV_CALL);
   endmethod

   method Word   read_gpr  (RegName r);
      return ((r == 0) ? 0 : regfile.sub (r));
   endmethod

   method Action write_gpr (RegName r, Word value);
      if (r != 0)
	 regfile.upd (r, value);
   endmethod

   method Word   read_pc;
      return pc;
   endmethod

   method Action write_pc  (Addr pc_value);
      pc <= pc_value;
   endmethod

   method Word   read_csr  (CSR_Addr csr_addr);
      if (fv_read_csr (csr_addr) matches tagged Valid .v)
	 return v;
      else
	 return 0;
   endmethod

   method Action write_csr (CSR_Addr csr_addr, Word csr_value);
      fa_write_csr (csr_addr, csr_value);
   endmethod
endmodule  

// ================================================================

endpackage
