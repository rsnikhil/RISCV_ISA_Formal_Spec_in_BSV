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

// ================================================================
// BSV project imports

import ISA_Decls :: *;    // Instruction encodings
import RegFiles  :: *;    // GPRs and CSRs
import DM_Common :: *;    // Debug Module defs

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
   method Bool   stopped;
   method Action stop_req;

   // Non-deterministic external request to increment "CYCLE" counter
   method Action csr_mcycle_incr;

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

   // Stop- and step-requests
   Reg #(Bool) rg_stop_req <- mkReg (False);    // stop-request from debugger
   Reg #(Bool) rg_step_req <- mkReg (False);    // step-request from dcsr.step

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
	 // Write Rd if present and not reg 0
	 if (maybe_rd_rdval matches tagged Valid { .rd, .rd_val }) begin
	    if (cfg_verbosity > 1)
	       $display ("    fa_finish_normal: rd %0d rd_val 0x%08h", rd, rd_val);

	    if (rd != 0)
	       regfiles.write_rd (rd, rd_val);
	 end

	 regfiles.csr_minstret_incr;

	 pc <= fv_fall_through_pc (pc);

	 cpu_state <= STATE_FETCH;
      endaction
   endfunction

   // ----------------
   // Finish csrrx instr:
   //  - Update Rd
   //  - Update CSR if upd_csr

   function Action fa_finish_csrrx (RegName rd, Word rd_val, Maybe #(Tuple2 #(CSR_Addr, Word)) m_csr_csr_val);
      action
	 // Write Rd, if not x0
	 if (rd != 0) begin
	    regfiles.write_rd (rd, rd_val);
	    if (cfg_verbosity > 1)
	       $display ("    fa_finish_csrrx: gpr [rd 0x%0h] <= rd_val 0x%0h", rd, rd_val);
	 end
	 else begin
	    if (cfg_verbosity > 1)
	       $display ("    fa_finish_csrrx: rd = 0; register write ignored");
	 end

	 // Update CSR, if given
	 if (m_csr_csr_val matches tagged Valid { .csr, .csr_val }) begin
	    Bool incr_minstret = (csr != csr_minstret);
	    regfiles.write_csr (csr, csr_val, incr_minstret);

	    if (cfg_verbosity > 1) begin
	       if (incr_minstret)
		  $display ("    fa_finish_csrrx: CSRRX: csr [0x%0h] <= 0x%08h; overriding normal increment", csr, csr_val);
	       else
		  $display ("    fa_finish_csrrx: CSRRX: csr [instret] <= 0x%08h; overriding normal increment", csr_val);
	    end
	 end

	 pc <= fv_fall_through_pc (pc);

	 cpu_state <= STATE_FETCH;
      endaction
   endfunction

   // ----------------
   // Finish conditional branch instr: incr instret, set PC, go to FETCH state

   function Action fa_finish_cond_branch (Bool branch_taken, Addr next_pc);
      action
	 if (cfg_verbosity > 1)
	    $display ("    fa_finish_cond_branch: Taken %0d, pc 0x%0h, next_pc 0x%0h",
		      pack (branch_taken), pc, next_pc);

	 regfiles.csr_minstret_incr;
	 pc <= (branch_taken ? next_pc : fv_fall_through_pc (pc));
	 cpu_state <= STATE_FETCH;
      endaction
   endfunction

   // ----------------
   // Finish jump instrs; write Rd, incr instret, set PC, go to FETCH state

   function Action fa_finish_jump (RegName rd, Word rd_value, Addr next_pc);
      action
	 if (cfg_verbosity > 1)
	    $display ("    fa_finish_jump: Rd 0x%0h, rd_value 0x%0h, next_pc 0x%0h",
		      rd, rd_value, next_pc);

	 // Simulation only: Special case: inifinite trap loop
	 if (pc == next_pc) begin
	    $display ("RISCV_Spec.fa_finish_jump: jump to current pc 0x%08h (infinite jump loop); exiting", pc);
	    $finish (1);
	 end

	 if (rd != 0)
	    regfiles.write_rd (rd, rd_value);

	 regfiles.csr_minstret_incr;
	 pc <= next_pc;

	 cpu_state <= STATE_FETCH;
      endaction
   endfunction

   // ----------------
   // Finish trap

   function Action fa_finish_trap (Word epc, Exc_Code exc_code, Addr badaddr);
      action
	 // Special case: BREAK in m-mode takes us into a debug stop
	 if (   regfiles.dcsr_break_enters_debug (rg_cur_priv)
	     && (exc_code == exc_code_BREAKPOINT))
	    begin
	       $display ("RISCV_Spec.fa_finish_trap: BREAK at pc 0x%08h; entering Debug Mode", pc);
	       regfiles.write_dcsr_cause (DCSR_CAUSE_EBREAK);
	       cpu_state <= STATE_IDLE;
	    end

	 // Normal case
	 else begin
	    if ((cfg_verbosity != 0) || (exc_code == exc_code_ILLEGAL_INSTRUCTION))
	       $display ("    fa_finish_trap: epc = 0x%0h, exc_code = 0x%0h, badaddr = 0x%0h",
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

	    // Simulation only: Special case: inifinite trap loop
	    if (epc == next_pc) begin
	       $display ("fa_finish_trap: infinite trap loop. 1st instr in trap-handler, at pc 0x%08h is illegal; exiting",
			 epc);
	       $finish (1);
	    end

	    // Accounting: increment minstret if ECALL
	    // ECALL is the only trapping instr for which we increment minstret
	    if (   (exc_code >= exc_code_ECALL_FROM_U)
		&& (exc_code <= exc_code_ECALL_FROM_M))
	       regfiles.csr_minstret_incr;

	    cpu_state <= STATE_FETCH;
	 end
      endaction
   endfunction

   // ----------------
   // Finish interrupt

   function Action fa_finish_interrupt (Word epc, Exc_Code exc_code);
      action
	 if ((cfg_verbosity != 0) || (exc_code == exc_code_ILLEGAL_INSTRUCTION))
	    $display ("    fa_finish_interrupt: epc = 0x%0h, exc_code = 0x%0h",
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
	    $display ("    fa_finish_WFI");

	 regfiles.csr_minstret_incr;
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

	 // ----------------------------------------------------------------
	 // Upper Immediate instructions

	 function Action fa_exec_LUI ();
	    action
	       Bit #(32)  v32   = { decoded.imm20_U, 12'h0 };
	       Word_S     iv    = extend (unpack (v32));    // sign-extend
	       let        value = pack (iv);                // back to unsigned

	       if (cfg_verbosity > 1)
		  $display ("    fa_exec_LUI: value 0x%08h", iv);

	       fa_finish_normal (tagged Valid (tuple2 (decoded.rd, value)));
	    endaction
	 endfunction: fa_exec_LUI

	 function Action fa_exec_AUIPC ();
	    action
	       Bit #(32) v32     = { decoded.imm20_U, 12'h0 };
	       Word_S    iv      = extend (unpack (v32));   // sign-extend
	       Word_S    pc_s    = unpack (pc);             // signed PC
	       Word_S    value_s = pc_s + iv;               // signed add
	       Word      value   = pack (value_s);          // back to unsigned

	       if (cfg_verbosity > 1)
		  $display ("    fa_exec_AUIPC: offset 0x%08h", iv);

	       fa_finish_normal (tagged Valid (tuple2 (decoded.rd, value)));
	    endaction
	 endfunction: fa_exec_AUIPC

	 // ----------------------------------------------------------------
	 // Control-transfer instructions (branch and jump)

	 function Action fa_exec_JAL ();
	    action
	       Word_S offset  = extend (unpack (decoded.imm21_UJ));
	       Addr   next_pc = pack (unpack (pc) + offset);

	       if (cfg_verbosity > 1)
		  $display ("    fa_exec_JAL: offset 0x%08h; target 0x%08h", offset, next_pc);

	       fa_finish_jump (decoded.rd, fv_fall_through_pc (pc), next_pc);
	    endaction
	 endfunction: fa_exec_JAL

	 function Action fa_exec_JALR ();
	    action
	       Word_S offset  = extend (unpack (decoded.imm12_I));
	       Addr   next_pc = pack (s_v1 + offset);

	       if (cfg_verbosity > 1)
		  $display ("    fa_exec_JALR: offset 0x%08h; target 0x%08h", offset, next_pc);

	       fa_finish_jump (decoded.rd, fv_fall_through_pc (pc), next_pc);
	    endaction
	 endfunction: fa_exec_JALR

	 function Action fa_exec_BRANCH ();
	    action
	       Word_S offset  = extend (unpack (decoded.imm13_SB));
	       Word   next_pc = pack (unpack (pc) + offset);

	       if (cfg_verbosity > 1)
		  $display ("    fa_exec_BRANCH: offset 0x%08h; target 0x%08h", offset, next_pc);

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

		     if (cfg_verbosity > 1)
			$display ("    fa_exec_LD_req: mem_addr 0x%08h size ",
				  mem_addr, fshow (sz));
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

		     if (cfg_verbosity > 1)
			$display ("    fa_exec_ST_req: mem_addr 0x%08h data 0x%08h size ",
				  mem_addr, v2, fshow (sz));
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
	       Word                v2    = zeroExtend (decoded.imm12_I);
	       Word_S              s_v2  = signExtend (unpack (decoded.imm12_I));
	       Bit #(TLog #(XLEN)) shamt = truncate (decoded.imm12_I);

	       if (cfg_verbosity > 1)
		  $display ("    fa_exec_OP_IMM: v1 0x%08h v2 0x%08h    (shamt %d for shifts)",
			    s_v1, s_v2, shamt);

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
	       Bit #(TLog #(XLEN)) shamt = truncate (v2);    // Caveat: upper bits are unspecified, per spec doc

	       if (cfg_verbosity > 1)
		  $display ("    fa_exec_OP: v1 0x%08h v2 0x%08h    (shamt %0d for shifts)",
			    s_v1, s_v2, shamt);

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
	       Word                v2      = zeroExtend (decoded.imm12_I);
	       Word_S              s_v2    = signExtend (unpack (decoded.imm12_I));
	       Int #(32)           s_v2_32 = signExtend (unpack (decoded.imm12_I));
	       Bit #(TLog #(XLEN)) shamt   = truncate (decoded.imm12_I);

	       if (cfg_verbosity > 1)
		  $display ("    fa_exec_OP_IMM_32: v1 0x%08h v2 0x%08h    (shamt %0d for shifts)",
			    s_v1_32, s_v2_32, shamt);

	       if (decoded.funct3 == f3_ADDIW) begin
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
	       Bit #(TLog #(XLEN)) shamt = truncate (v2);    // Caveat: upper bits are unspecified, per spec doc

	       if (cfg_verbosity > 1)
		  $display ("    fa_exec_OP_32: v1 0x%08h v2 0x%08h    (shamt %0d for shifts)",
			    s_v1_32, s_v2_32, shamt);

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
	 // Implemented as split-phase no-ops (send msg to memory
	 // system, receive response).

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
			$display ("    fa_exec_MISC_MEM.FENCE");
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
			$display ("    fa_exec_MISC_MEM.FENCE_I");
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
	       // The following are symbolic names for args to csr_ok
	       Bool rw_csrrw   = True;                  // CSRRW, CSRRWI always write to CSR
	       Bool rw_csrr_sc = (decoded.rs1 != 0);    // CSRRS, CSRRSI, CSRRC, CSRRCI write to CSR if rs1!=0

	       // ECALL
	       if      (   (decoded.funct3 == f3_PRIV)
			&& (decoded.imm12_I == f12_ECALL)
			&& (decoded.rs1 == 0)
			&& (decoded.rd == 0))
		  begin
		     Exc_Code exc_code = (  (rg_cur_priv == u_Priv_Mode)
					  ? exc_code_ECALL_FROM_U
					  : exc_code_ECALL_FROM_M);

		     if (cfg_verbosity > 1)
			$display ("    fa_exec_SYSTEM: ECALL");

		     fa_finish_trap (pc, exc_code, ?);
		  end

	       // EBREAK
	       else if (   (decoded.funct3 == f3_PRIV)
			&& (decoded.imm12_I == f12_EBREAK)
			&& (decoded.rs1 == 0)
			&& (decoded.rd == 0))
		  begin
		     if (cfg_verbosity > 1)
			$display ("    fa_exec_SYSTEM: EBREAK");

		     fa_finish_trap (pc, exc_code_BREAKPOINT, ?);
		  end

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

		     if (cfg_verbosity > 1)
			$display ("    fa_exec_SYSTEM: MRET: new mstatus 0x%08h new priv ",
				  new_mstatus, fshow (new_priv));

		     fa_finish_cond_branch (True /* branch taken */, next_pc);
		  end

	       // WFI
	       else if (   (decoded.funct3 == f3_PRIV)
			&& (rg_cur_priv == m_Priv_Mode)
			&& (decoded.imm12_I == f12_WFI)
			&& (decoded.rs1 == 0)
			&& (decoded.rd == 0))
		  begin
		     if (cfg_verbosity > 1)
			$display ("    fa_exec_SYSTEM: WFI");
		     fa_finish_WFI;
		  end

	       // CSRRW
	       else if (   (decoded.funct3 == f3_CSRRW)
			&& regfiles.csr_ok_port1 (decoded.csr, rg_cur_priv, rw_csrrw))
		  begin
		     Word csr_new_val = v1;

		     // Read the CSR only if rd is not x0
		     Word csr_old_val;
		     if (decoded.rd != 0) begin
			Word x <- regfiles.av_read_csr (decoded.csr);    // Note: already checked csr access
			csr_old_val = x;
		     end
		     else
			csr_old_val = ?;

		     fa_finish_csrrx (decoded.rd, csr_old_val, tagged Valid tuple2 (decoded.csr, csr_new_val));
		  end

	       // CSRRWI
	       else if (   (decoded.funct3 == f3_CSRRWI)
			&& regfiles.csr_ok_port1 (decoded.csr, rg_cur_priv, rw_csrrw))
		  begin
		     Word csr_new_val = zeroExtend (decoded.rs1);

		     // Read the CSR only if rd is not x0
		     Word csr_old_val;
		     if (decoded.rd != 0) begin
			Word x <- regfiles.av_read_csr (decoded.csr);    // Note: already checked csr access
			csr_old_val = x;
		     end
		     else
			csr_old_val = ?;

		     fa_finish_csrrx (decoded.rd, csr_old_val, tagged Valid tuple2 (decoded.csr, csr_new_val));
		  end

	       // CSRRS
	       else if (   (decoded.funct3 == f3_CSRRS)
			&& regfiles.csr_ok_port2 (decoded.csr, rg_cur_priv, rw_csrr_sc))
		  begin
		     Word csr_old_val <- regfiles.av_read_csr (decoded.csr);    // Note: already checked csr access

		     Maybe #(Tuple2 #(CSR_Addr, Word)) m_csr_csr_new_val = tagged Invalid;
		     if (decoded.rs1 != 0) begin
			Word csr_new_val = (csr_old_val | v1);
			m_csr_csr_new_val = tagged Valid tuple2 (decoded.csr, csr_new_val);
		     end
		  
		     fa_finish_csrrx (decoded.rd, csr_old_val, m_csr_csr_new_val);
		  end

	       // CSRRSI
	       else if (   (decoded.funct3 == f3_CSRRSI)
			&& regfiles.csr_ok_port2 (decoded.csr, rg_cur_priv, rw_csrr_sc))
		  begin
		     Word csr_old_val <- regfiles.av_read_csr (decoded.csr);    // Note: already checked csr access
		     Word v1 = zeroExtend (decoded.rs1);

		     Maybe #(Tuple2 #(CSR_Addr, Word)) m_csr_csr_new_val = tagged Invalid;
		     if (decoded.rs1 != 0) begin
			Word csr_new_val = (csr_old_val | v1);
			m_csr_csr_new_val = tagged Valid tuple2 (decoded.csr, csr_new_val);
		     end
		  
		     fa_finish_csrrx (decoded.rd, csr_old_val, m_csr_csr_new_val);
		  end

	       // CSRRC
	       else if (   (decoded.funct3 == f3_CSRRC)
			&& regfiles.csr_ok_port2 (decoded.csr, rg_cur_priv, rw_csrr_sc))
		  begin
		     Word csr_old_val <- regfiles.av_read_csr (decoded.csr);    // Note: already checked csr access

		     Maybe #(Tuple2 #(CSR_Addr, Word)) m_csr_csr_new_val = tagged Invalid;
		     if (decoded.rs1 != 0) begin
			Word csr_new_val = (csr_old_val & (~ v1));
			m_csr_csr_new_val = tagged Valid tuple2 (decoded.csr, csr_new_val);
		     end
		  
		     fa_finish_csrrx (decoded.rd, csr_old_val, m_csr_csr_new_val);
		  end

	       // CSRRCI
	       else if (   (decoded.funct3 == f3_CSRRCI)
			&& regfiles.csr_ok_port2 (decoded.csr, rg_cur_priv, rw_csrr_sc))
		  begin
		     Word csr_old_val <- regfiles.av_read_csr (decoded.csr);    // Note: already checked csr access
		     Word v1 = zeroExtend (decoded.rs1);

		     Maybe #(Tuple2 #(CSR_Addr, Word)) m_csr_csr_new_val = tagged Invalid;
		     if (decoded.rs1 != 0) begin
			Word csr_new_val = (csr_old_val & (~ v1));
			m_csr_csr_new_val = tagged Valid tuple2 (decoded.csr, csr_new_val);
		     end
		  
		     fa_finish_csrrx (decoded.rd, csr_old_val, m_csr_csr_new_val);
		  end

	       else begin
		  if (cfg_verbosity > 1)
		     $display ("    fa_exec_SYSTEM: illegal SYSTEM instruction");
		  fa_finish_trap (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
	       end
	    endaction
	 endfunction: fa_exec_SYSTEM

	 // ----------------------------------------------------------------
	 // Main body of fa_exec(), dispatching to the sub functions
	 // based on major OPCODE

	 if (cfg_verbosity != 0)
	    $display ("    fa_exec: pc 0x%08h instr 0x%0h", pc, instr);

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

	 else begin
	    if (cfg_verbosity > 1)
	       $display ("    illegal instruction");
	    fa_finish_trap (pc, exc_code_ILLEGAL_INSTRUCTION, ?);
	 end
      endaction
   endfunction: fa_exec

   // ================================================================
   // The CPU's top-level state machine

   // ---------------- FETCH
   // Issue instruction request
   // (provided there is no interrupt or stop-request pending)

   rule rl_fetch (cpu_state == STATE_FETCH);
      // Take debugger stop-request, if present
      if (rg_stop_req) begin
	 $display ("RISCV_Spec.rl_fetch: Stop for debugger: pc 0x%08h", pc);
	 regfiles.write_dpc (pc);
	 regfiles.write_dcsr_cause (DCSR_CAUSE_HALTREQ);
	 rg_stop_req <= False;
	 cpu_state   <= STATE_IDLE;
      end

      // Stop due to single-step request (dcsr.step)
      else if (rg_step_req) begin
	 $display ("RISCV_Spec.rl_fetch: Stop after single-step: pc 0x%08h", pc);
	 regfiles.write_dpc (pc);
	 regfiles.write_dcsr_cause (DCSR_CAUSE_STEP);
	 rg_step_req <= False;
	 cpu_state   <= STATE_IDLE;
      end

      // Take external interrupt, if present
      else if (regfiles.interrupt_pending (rg_cur_priv) matches tagged Valid .exc_code) begin
	 if (cfg_verbosity > 1)
	    $display ("RISCV_Spec.rl_fetch: Taking external interrupt w. exc_code %0d; pc 0x%08h",
		      exc_code, pc);
	 fa_finish_interrupt (pc, exc_code);
      end

      // Normal instruction fetch
      else begin
	 if (cfg_verbosity > 1)
	    $display ("RISCV_Spec.rl_fetch: pc 0x%08h", pc);

	 memory.imem_req (pc);
	 cpu_state <= STATE_EXEC;

	 // If single-step mode, set step-request to cause a stop at next rl_fetch
	 if (regfiles.read_dcsr_step)
	    rg_step_req <= True;
      end
   endrule

   // ---------------- EXECUTE
   // Receive instruction from IMem; handle exception if any, else execute it;
   // for LD/ST, issue request and move to LD_RESPONSE/ST_RESPONSE state)

   rule rl_exec (cpu_state == STATE_EXEC);
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
      Decoded_Instr decoded = fv_decode (rg_instr);

      let resp <- memory.dmem_resp;

      if (cfg_verbosity > 1)
	 $display ("    rl_exec_LD_response: ", fshow (resp));

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
      DMem_Resp resp <- memory.dmem_resp;

      if (cfg_verbosity > 1)
	 $display ("    rl_exec_ST_response: ", fshow (resp));

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
	 $display ("    rl_exec_FENCE_I_response");

      fa_finish_normal (tagged Invalid);
   endrule

   // ---------------- FENCE-responses from DMem

   rule rl_exec_FENCE_response (cpu_state == STATE_EXEC_FENCE_RESPONSE);
      // Await mem system FENCE completion
      let dummy <- memory.server_fence.response.get;

      if (cfg_verbosity > 1)
	 $display ("    rl_exec_FENCE_response");

      fa_finish_normal (tagged Invalid);
   endrule

   // ---------------- WFI

   rule rl_exec_WFI (cpu_state == STATE_WFI);
      if (cfg_verbosity > 1)
	 $display ("    rl_exec_WFI");
   endrule

   // ----------------------------------------------------------------
   // INTERFACE

   // ----------------
   // Reset

   method Action reset;
      rg_cur_priv <= m_Priv_Mode;
      rg_stop_req <= False;
   endmethod

   // ----------------
   // Run control

   method Action start;
      cpu_state <= STATE_FETCH;
   endmethod

   method Bool stopped;
      return (cpu_state == STATE_IDLE);
   endmethod

   method Action stop_req;
      rg_stop_req <= True;
   endmethod

   // ----------------
   // Non-deterministic external request to increment "CYCLE" counter

   method Action csr_mcycle_incr;
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
      Bool incr_minstret = False;
      regfiles.write_csr (csr_addr, csr_value, incr_minstret);
   endmethod
endmodule  

// ================================================================

endpackage
