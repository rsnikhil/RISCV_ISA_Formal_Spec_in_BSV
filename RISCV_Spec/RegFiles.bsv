// Copyright (c) 2016-2017 Bluespec, Inc. All Rights Reserved

package RegFiles;

// ================================================================
// GPR (General Purpose Register) Register File
// CSR (Control and Status Register) Register File

// ================================================================
// Exports

export RegFiles_IFC (..), mkRegFiles;

// ================================================================
// BSV library imports

import ConfigReg    :: *;
import RegFile      :: *;
import FIFOF        :: *;
import GetPut       :: *;
import ClientServer :: *;

// BSV additional libs

import Cur_Cycle  :: *;
import GetPut_Aux :: *;

// ================================================================
// Project imports

import ISA_Decls :: *;
import DM_Common :: *;    // Debug Module defs

// ================================================================
// Interface of the register file

interface RegFiles_IFC;
   // Reset
   interface Server #(Token, Token) server_reset;

   // ----------------
   // GPR access

   // GPR read
   method Word read_rs1 (RegName rs1);
   method Word read_rs1_port2 (RegName rs1);    // For debugger access only
   method Word read_rs2 (RegName rs2);

   // GPR write
   method Action write_rd (RegName rd, Word rd_val);

   // ----------------
   // CSR access

   // Is a particular CSR available and accessible at the given privilege level for RW/RO?
   method Bool csr_ok_port1 (CSR_Addr csr_addr, Priv_Mode priv, Bool rw);
   method Bool csr_ok_port2 (CSR_Addr csr_addr, Priv_Mode priv, Bool rw);

   // CSR read (w.o. side effect)
   method Maybe #(Word) read_csr (CSR_Addr csr_addr);
   method Maybe #(Word) read_csr_port2 (CSR_Addr csr_addr);

   // ActionValue CSR read (possible side effect on read)
   // Note: called only after checking that access to csr_addr is ok.
   method ActionValue #(Word) av_read_csr (CSR_Addr csr_addr);

   // CSR write
   // This is only called after checking if writing to csr_addr is valid.
   // The only subtlety concerns csr_minstret
   // When csr_addr == csr_minstret/csr_minstreth:
   // - it is never incremented, whether written by a CSRRx instr or by the debugger
   // When csr_addr != csr_minstret/csr_minstreth. Then, csr_minstret
   // - is incremented when the CPU writes other CSRs
   // - is not incremented when the debugger writes other CSRs
   // This is controlled by the flag incr_minstret.
   method Action write_csr (CSR_Addr csr_addr, Word word, Bool incr_minstret);

   // CSR trap actions
   method ActionValue #(Tuple3 #(Addr, Word, Word)) csr_trap_actions (Priv_Mode  from_priv,
								      Priv_Mode  to_priv,
								      Word       pc,
								      Bool       interrupt,
								      Exc_Code   exc_code,
								      Word       badaddr);

   // CSR RET actions (return from exception)
   method ActionValue #(Tuple3 #(Addr, Priv_Mode, Word)) csr_ret_actions (Priv_Mode from_priv);

   // Read MINSTRET
   method Bit #(64) read_csr_minstret;

   // Increment MINSTRET
   method Action csr_minstret_incr;

   // Read TIME
   method Bit #(64) read_csr_time;

   // Read MCOUNTEREN
   method MCounteren read_csr_mcounteren;

   // Read MCYCLE
   method Bit #(64) read_csr_mcycle;

   // Increment MCYCLE
   method Action csr_mcycle_incr;

   // Read dpc
   method Word read_dpc ();

   // Update dpc
   method Action write_dpc (Addr pc);

   // Break should enter Debug Mode
   method Bool dcsr_break_enters_debug (Priv_Mode cur_priv);

   // Read dcsr.step
   method Bool read_dcsr_step ();

   // Update 'cause' in DCSR
   method Action write_dcsr_cause (DCSR_Cause cause);

   // External interrupt
   method Action external_interrupt_req;

   method Maybe #(Exc_Code) interrupt_pending (Priv_Mode cur_priv);
endinterface

// ================================================================
// 'misa' for RISC-V Spec, specifying RSIC-V features implemented.

function MISA misa_RISCV_Spec;
   MISA ms = unpack (0);

`ifdef RV32
   ms.mxl = misa_mxl_32;
`elsif RV64
   ms.mxl = misa_mxl_64;
`elsif RV128
   ms.mxl = misa_mxl_128;
`else
   ms.mxl = misa_mxl_default;
`endif

   ms.u = 1'b1;

`ifdef ISA_M
   ms.m = 1'b1;
`else
   ms.m = 1'b0;
`endif

   ms.i = 1'b1;

`ifdef ISA_FD
   ms.f = 1'b1;
   ms.d = 1'b1;
`else
   ms.f = 1'b0;
   ms.d = 1'b0;
`endif

`ifdef ISA_A
   ms.a = 1'b1;
`else
   ms.a = 1'b0;
`endif

   return ms;
endfunction

// ================================================================
// mtvec and PC reset values
// MTVEC reg can be hardwired to hi or lo value
// reset value should correspond.

Word mtvec_std_lo = 'h0100;
Word mtvec_std_hi = (~ 'h01FF);    // = 0xF...FFE00

`ifdef MTVEC_STD_HI
   Word mtvec_reset_value = mtvec_std_hi;
`else
   Word mtvec_reset_value = mtvec_std_lo;
`endif

Word pc_reset_value = (mtvec_reset_value + 'h100);    // 'h0200 or 'hFFFF....F00

// ================================================================
// Major states of mkRegFiles module

typedef enum { RF_RESET_START, RF_RESETTING, RF_RUNNING } RF_State
deriving (Eq, Bits, FShow);

// ================================================================

(* synthesize *)
module mkRegFiles (RegFiles_IFC);

   Reg #(Bit #(4)) cfg_verbosity <- mkConfigReg (0);
   Reg #(RF_State) rg_state      <- mkReg (RF_RESET_START);

   // Reset
   FIFOF #(Token) f_reset_rsps <- mkFIFOF;

   // General Purpose Registers
   RegFile #(RegName, Word) regfile <- mkRegFileFull;

`ifdef ISA_PRIV_M
   // CSRs
   // Machine-level
   Word mvendorid   = 0;    // Not implemented
   Word marchid     = 0;    // Not implemented
   Word mimpid      = 0;    // Not implemented
   Word mhartid     = 0;

   Reg #(MStatus) rg_mstatus  <- mkReg (mstatus_reset_value);
   MISA           misa        = misa_RISCV_Spec;
   Reg #(MIE)     rg_mie      <- mkRegU;
   Reg #(MTVec)   rg_mtvec    <- mkRegU;
   Reg #(Word)    rg_mscratch <- mkRegU;
   Reg #(Word)    rg_mepc     <- mkRegU;
   Reg #(MCause)  rg_mcause   <- mkRegU;
   Reg #(Word)    rg_mtval    <- mkRegU;
   Reg #(MIP)     rg_mip      <- mkRegU;
`endif

   Reg #(Bit #(64)) rg_mcycle   <- mkReg (0);
   Reg #(Bit #(64)) rg_minstret <- mkReg (0);

`ifdef ISA_PRIV_M
   Reg #(MCounteren) rg_mcounteren <- mkRegU;
`endif

   Reg #(Word) rg_dpc  <- mkRegU;
   Reg #(Word) rg_dcsr <- mkRegU;

   // ----------------------------------------------------------------
   // Reset.
   // Initialize all GPRs to 0 (not necessary per spec, but useful for debugging)
   // Initialize some CSRs.

   Reg #(RegName) rg_j <- mkRegU;

   rule rl_reset_start (rg_state == RF_RESET_START);
      rg_state    <= RF_RESETTING;
      rg_minstret <= 0;

`ifdef ISA_PRIV_M
      rg_mstatus  <= mstatus_reset_value;
      rg_mie      <= word_to_mie (0);
      rg_mtvec    <= word_to_mtvec (mtvec_reset_value);
      rg_mcause   <= word_to_mcause (0);    // Supposed to be the cause of the reset.
      rg_mip      <= word_to_mip (0);
      rg_mcounteren <= mcounteren_reset_value;
`endif

      rg_dpc  <= pc_reset_value;
      rg_dcsr <= {4'h4,    // xdebugver
		  12'h0,   // reserved
		  1'h1,    // ebreakm
		  1'h0,    // reserved
		  1'h1,    // ebreaks
		  1'h1,    // ebreaku
		  1'h0,    // stepie
		  1'h0,    // stepcount
		  1'h0,    // steptime
		  3'h0,    // cause    // WARNING: 0 is non-standard
		  3'h0,    // reserved
		  1'h0,    // step
		  2'h0};   // prv

      rg_j <= 1;
   endrule

   rule rl_reset_loop (rg_state == RF_RESETTING);
      regfile.upd (rg_j, 0);
      rg_j <= rg_j + 1;

      if (rg_j == 31)
	 rg_state <= RF_RUNNING;
   endrule

   // ----------------------------------------------------------------
   // Help functions for interface methods

   // ----------------
   // Is a particular CSR available and accessible at the given privilege level for RW/RO?

   function Bool fv_csr_ok (CSR_Addr csr_addr, Priv_Mode priv, Bool rw);

      // Check privilege level ok, based on csr_addr bits
      if (! fn_csr_addr_priv_ok (csr_addr, priv))
	 return False;

      // Check if R/W ok, based on csr_addr bits
      else if (rw && (! fn_csr_addr_can_write (csr_addr)))
	 return False;

      // Check if specific reg is implemented
      else
	 return (   (csr_addr == csr_cycle)
		 || (csr_addr == csr_instret)
`ifdef RV32
		 || (csr_addr == csr_cycleh)
		 || (csr_addr == csr_instreth)
`endif

`ifdef ISA_FD
	         || (csr_addr == csr_fflags)
		 || (csr_addr == csr_frm)
		 || (csr_addr == csr_fcsr)
`endif

`ifdef ISA_PRIV_M
		 || (csr_addr == csr_mvendorid)
		 || (csr_addr == csr_marchid)
		 || (csr_addr == csr_mimpid)
		 || (csr_addr == csr_mhartid)
		 || (csr_addr == csr_mstatus)
		 || (csr_addr == csr_misa)
		 || (csr_addr == csr_mie)
		 || (csr_addr == csr_mtvec)
		 || (csr_addr == csr_mscratch)
		 || (csr_addr == csr_mepc)
		 || (csr_addr == csr_mcause)
		 || (csr_addr == csr_mtval)
		 || (csr_addr == csr_mip)
		 || (csr_addr == csr_mcounteren)
`endif

		 || (csr_addr == csr_mcycle)
		 || (csr_addr == csr_minstret)
`ifdef RV32
		 || (csr_addr == csr_mcycleh)
		 || (csr_addr == csr_minstreth)
`endif
		 || (csr_addr == csr_addr_dpc)
		 || (csr_addr == csr_addr_dcsr));
   endfunction
   
   // ----------------
   // CSR reads (no side effect)
   // Returns Invalid for invalid CSR addresses or access-mode violations

   function Maybe #(Word) fv_csr_read (CSR_Addr csr_addr);
      Maybe #(Word)  m_csr_value = tagged Invalid;

      case (csr_addr)
	 // User mode csrs
`ifdef ISA_FD
	 csr_fflags:    m_csr_value = tagged Valid 0;
	 csr_frm:       m_csr_value = tagged Valid 0;
	 csr_fcsr:      m_csr_value = tagged Valid 0;
`endif

	 csr_cycle:     m_csr_value = tagged Valid (truncate (rg_mcycle));
	 csr_instret:   m_csr_value = tagged Valid (truncate (rg_minstret));
`ifdef RV32
	 csr_cycleh:    m_csr_value = tagged Valid (rg_mcycle   [63:32]);
	 csr_instreth:  m_csr_value = tagged Valid (rg_minstret [63:32]);
`endif

`ifdef ISA_PRIV_M
	 // Machine mode csrs
	 csr_mvendorid: m_csr_value = tagged Valid mvendorid;
	 csr_marchid:   m_csr_value = tagged Valid marchid;
	 csr_mimpid:    m_csr_value = tagged Valid mimpid;
	 csr_mhartid:   m_csr_value = tagged Valid mhartid;

	 csr_mstatus:   m_csr_value = tagged Valid (mstatus_to_word (rg_mstatus));
	 csr_misa:      m_csr_value = tagged Valid (misa_to_word (misa));
	 csr_mie:       m_csr_value = tagged Valid (mie_to_word (rg_mie));
	 csr_mtvec:     m_csr_value = tagged Valid (mtvec_to_word (rg_mtvec));

	 csr_mscratch:  m_csr_value = tagged Valid rg_mscratch;
	 csr_mepc:      m_csr_value = tagged Valid rg_mepc;
	 csr_mcause:    m_csr_value = tagged Valid (mcause_to_word (rg_mcause));
	 csr_mtval:     m_csr_value = tagged Valid rg_mtval;
	 csr_mip:       m_csr_value = tagged Valid (mip_to_word (rg_mip));
	 csr_mcounteren:m_csr_value = tagged Valid (mcounteren_to_word (rg_mcounteren));
`endif

	 csr_mcycle:    m_csr_value = tagged Valid (truncate (rg_mcycle));
	 csr_minstret:  m_csr_value = tagged Valid (truncate (rg_minstret));
`ifdef RV32
	 csr_mcycleh:   m_csr_value = tagged Valid (rg_mcycle [63:32]);
	 csr_minstreth: m_csr_value = tagged Valid (rg_minstret [63:32]);
`endif

	 csr_addr_dpc:  m_csr_value = tagged Valid rg_dpc;
	 csr_addr_dcsr: m_csr_value = tagged Valid rg_dcsr;

	 default: m_csr_value = tagged Invalid;
      endcase
      return m_csr_value;
   endfunction
   
   // ----------------
   // CSR writes

   function Action fav_write_csr (CSR_Addr csr_addr, Word word, Bool incr_minstret);
      action
	 if (csr_addr == csr_minstret)
	    rg_minstret <= { rg_minstret [63:32], word };
`ifdef RV32
	 else if (csr_addr == csr_minstreth)
	    rg_minstret <= { word, rg_minstret [31:0] };
`endif
	 else begin
	    case (csr_addr)
	       // User mode csrs
`ifdef ISA_FD
	       csr_fflags:    noAction;
	       csr_frm:       noAction;
	       csr_fcsr:      noAction;
`endif

`ifdef ISA_PRIV_M
	       // Machine mode
	       csr_mvendorid: noAction;
	       csr_marchid:   noAction;
	       csr_mimpid:    noAction;
	       csr_mhartid:   noAction;

	       csr_mstatus:   rg_mstatus <= word_to_mstatus (word);
	       csr_misa:      noAction;
	       csr_mie:       rg_mie   <= word_to_mie (word);
	       csr_mtvec:     rg_mtvec <= word_to_mtvec(word);

	       csr_mscratch:  rg_mscratch <= word;
	       csr_mepc:      rg_mepc <= word;
	       csr_mcause:    rg_mcause <= word_to_mcause (word);
	       csr_mtval:     rg_mtval <= word;
	       csr_mip:       rg_mip <= word_to_mip (word);
	       csr_mcounteren:rg_mcounteren <= word_to_mcounteren(word);
`endif

	       csr_mcycle:    rg_mcycle   <= { rg_mcycle   [63:32], word };

`ifdef RV32
	       csr_mcycleh:   rg_mcycle   <= { word, rg_mcycle   [31:0] };
`endif

	       csr_addr_dpc:  rg_dpc  <= word;
	       csr_addr_dcsr: rg_dcsr <= {rg_dcsr [31:28],    // xdebugver: read-only
					  word [27:9],        // ebreakm/s/u, stepie, stopcount, stoptime
					  rg_dcsr [8:6],      // cause: read-only
					  word [5:0]};        // step, prv
	    endcase
	    if (incr_minstret)
	       rg_minstret <= rg_minstret + 1;
	 end
      endaction
   endfunction

   // ----------------------------------------------------------------
   // INTERFACE

   // Reset
   interface Server server_reset;
      interface Put request;
	 method Action put (Token token);
	    rg_state <= RF_RESET_START;
	    f_reset_rsps.enq (?);
	 endmethod
      endinterface
      interface Get response;
	 method ActionValue #(Token) get if (rg_state == RF_RUNNING);
	    let token <- pop (f_reset_rsps);
	    return token;
	 endmethod
      endinterface
   endinterface

   // ----------------
   // GPR access

   // GPR read
   method Word read_rs1 (RegName rs1);
      return ((rs1 == 0) ? 0 : regfile.sub (rs1));
   endmethod

   // GPR read
   method Word read_rs1_port2 (RegName rs1);        // For debugger access only
      return ((rs1 == 0) ? 0 : regfile.sub (rs1));
   endmethod

   method Word read_rs2 (RegName rs2);
      return ((rs2 == 0) ? 0 : regfile.sub (rs2));
   endmethod

   // GPR write
   method Action write_rd (RegName rd, Word rd_val);
      if (rd != 0) regfile.upd (rd, rd_val);
   endmethod

   // ----------------
   // CSR access

   // Is a particular CSR available and accessible at the given privilege level for RW/RO?
   method Bool csr_ok_port1 (CSR_Addr csr_addr, Priv_Mode priv, Bool rw);
      return fv_csr_ok (csr_addr, priv, rw);
   endmethod

   method Bool csr_ok_port2 (CSR_Addr csr_addr, Priv_Mode priv, Bool rw);
      return fv_csr_ok (csr_addr, priv, rw);
   endmethod

   // CSR read (w.o. side effect)
   method Maybe #(Word) read_csr (CSR_Addr csr_addr);
      return fv_csr_read (csr_addr);
   endmethod

   method Maybe #(Word) read_csr_port2 (CSR_Addr csr_addr);
      return fv_csr_read (csr_addr);
   endmethod

   // CSR read (w. side effect)
   // Note: called only after checking that access to csr_addr is ok.
   method ActionValue #(Word) av_read_csr (CSR_Addr csr_addr);
      return fromMaybe (?, fv_csr_read (csr_addr));
   endmethod

   // CSR write
   method Action write_csr (CSR_Addr csr_addr, Word word, Bool incr_minstret);
      fav_write_csr (csr_addr, word, incr_minstret);
      // $display ("%0d: Regfiles.write_csr (0x%08h, 0x%08h)", cur_cycle, csr_addr, word);
   endmethod

   // CSR Trap actions
   method ActionValue #(Tuple3 #(Addr, Word, Word)) csr_trap_actions (Priv_Mode  from_priv,
								      Priv_Mode  to_priv,
								      Word       pc,
								      Bool       interrupt,
								      Exc_Code   exc_code,
								      Word       badaddr);
`ifdef ISA_PRIV_M
      let new_mstatus = fn_mstatus_upd_on_trap (rg_mstatus, from_priv, to_priv);
      rg_mstatus     <= new_mstatus;
      rg_mepc        <= pc;
      let mcause      = MCause {interrupt: pack (interrupt), exc_code: exc_code};
      rg_mcause      <= mcause;

      // MTVal is recorded only for exceptions
      if (!interrupt)
	 rg_mtval <= badaddr;
      
      // Compute the exception PC based on the MTVEC mode bits
      Addr exc_pc     = (extend (rg_mtvec.base)) << 2;
      Addr vector_offset = (extend (exc_code)) << 2;
      if ((interrupt) && (rg_mtvec.mode == VECTORED))
	 exc_pc = exc_pc + vector_offset;

      return tuple3 (exc_pc,
		     mstatus_to_word (new_mstatus),
		     mcause_to_word  (mcause));
`else
      return tuple3 (?, ?, ?);
`endif
   endmethod

   // CSR RET actions (return from exception)
   method ActionValue #(Tuple3 #(Addr, Priv_Mode, Word)) csr_ret_actions (Priv_Mode from_priv);
`ifdef ISA_PRIV_M
      match { .new_mstatus, .to_priv } = fn_mstatus_upd_on_ret (rg_mstatus, from_priv);
      rg_mstatus  <= new_mstatus;
      return tuple3 (rg_mepc, to_priv, mstatus_to_word (new_mstatus));
`else
      return tuple3 (?, ?, ?);
`endif
   endmethod

   // Read MINSTRET
   method Bit #(64) read_csr_minstret () if (rg_state == RF_RUNNING);
      return rg_minstret;
   endmethod

   // Increment MINSTRET
   method Action csr_minstret_incr;
      rg_minstret <= rg_minstret + 1;
   endmethod

   // Read TIME
   method Bit #(64) read_csr_time;
      // We use mcycle as a proxy for time
      return rg_mcycle;
   endmethod

   // Read MCOUNTEREN
   method MCounteren read_csr_mcounteren;
`ifdef ISA_PRIV_M
      return rg_mcounteren;
`else
      return ?;
`endif
   endmethod

   // Read MCYCLE
   method Bit #(64) read_csr_mcycle;
      return rg_mcycle;
   endmethod

   // Increment MCYCLE
   method Action csr_mcycle_incr;
      rg_mcycle <= rg_mcycle + 1;
   endmethod

   // Read dpc
   method Word read_dpc ();
      return rg_dpc;
   endmethod

   // Update dpc
   method Action write_dpc (Addr pc);
      rg_dpc <= pc;
   endmethod

   // Break should enter Debug Mode
   method Bool dcsr_break_enters_debug (Priv_Mode cur_priv);
      return case (cur_priv)
		m_Priv_Mode: (rg_dcsr [15] == 1'b1);
		s_Priv_Mode: (rg_dcsr [13] == 1'b1);
		u_Priv_Mode: (rg_dcsr [12] == 1'b1);
	     endcase;
   endmethod

   // Read dpc
   method Bool read_dcsr_step ();
      return unpack (rg_dcsr [2]);
   endmethod

   // Update 'cause' in DCSR
   method Action write_dcsr_cause (DCSR_Cause cause);
      Bit #(3) b3 = pack (cause);
      rg_dcsr <= { rg_dcsr [31:9], b3, rg_dcsr [5:0] };
   endmethod

   // ----------------
   // Interrupt methods

   // External interrupt
   method Action external_interrupt_req;
      let mip = rg_mip;
      mip.eips [m_Priv_Mode] = 1'b1;
      rg_mip <= mip;
   endmethod

   method Maybe #(Exc_Code) interrupt_pending (Priv_Mode cur_priv);
      return fn_interrupt_pending (mstatus_to_word (rg_mstatus),
				   mip_to_word     (rg_mip),
				   mie_to_word     (rg_mie),
				   cur_priv);
   endmethod

endmodule

// ================================================================

endpackage
