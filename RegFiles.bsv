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

import ISA_Decls   :: *;

// ================================================================

interface RegFiles_IFC;
   // Reset
   interface Server #(Token, Token) server_reset;

   // ----------------
   // Integer registers

   // GPR read
   (* always_ready *)
   method Word read_rs1 (RegName rs1);
   (* always_ready *)
   method Word read_rs1_port2 (RegName rs1);    // For debugger access only
   (* always_ready *)
   method Word read_rs2 (RegName rs2);

   // GPR write
   (* always_ready *)
   method Action write_rd (RegName rd, Word rd_val);

   // ----------------
   // CSRs

   // CSR read
   (* always_ready *)
   method Maybe #(Word) read_csr (CSR_Addr csr_addr);
   (* always_ready *)
   method ActionValue #(Maybe #(Word)) mav_read_csr (CSR_Addr csr_addr);

   // CSR write
   (* always_ready *)
   method Action write_csr (CSR_Addr csr_addr, Word word);

   // CSR trap actions
   method ActionValue #(Tuple3 #(Addr, Word, Word)) csr_trap_actions (Priv_Mode  from_priv,
								      Priv_Mode  to_priv,
								      Word       pc,
								      Bool       interrupt,
								      Exc_Code   exc_code,
								      Word       badaddr);

   // CSR RET actions (return from exception)
   method ActionValue #(Tuple3 #(Addr, Priv_Mode, Word)) csr_ret_actions (Priv_Mode from_priv);

   // Read INSTRET
   (* always_ready *)
   method Bit #(64) read_csr_instret;

   // Increment INSTRET
   (* always_ready *)
   method Action csr_instret_incr;

   // Read TIME
   (* always_ready *)
   method Bit #(64) read_csr_time;

   // Read MCOUNTEREN
   (* always_ready *)
   method MCounteren read_csr_mcounteren;

   // Read MCYCLE
   (* always_ready *)
   method Bit #(64) read_csr_mcycle;

   // Increment MCYCLE
   (* always_ready *)
   method Action csr_mcycle_incr;
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
// Major states of mkRegFiles module

typedef enum { RF_RESET_START, RF_RESETTING, RF_RUNNING } RF_State
deriving (Eq, Bits, FShow);

// ================================================================

(* synthesize *)
module mkRegFiles #(parameter Word mtvec_reset_value)
                  (RegFiles_IFC);

   Reg #(Bit #(4)) cfg_verbosity <- mkConfigReg (0);
   Reg #(RF_State) rg_state      <- mkReg (RF_RESET_START);

   // Reset
   FIFOF #(Token) f_reset_rsps <- mkFIFOF;

   // General Purpose Registers
   // TODO: can we use Reg [0] for some other purpose?
   RegFile #(RegName, Word) regfile <- mkRegFileFull;

`ifdef ISA_PRIV_M
   // CSRs
   // Machine-level
   Word mvendorid   = 0;    // Not implemented
   Word marchid     = 0;    // Not implemented
   Word mimpid      = 0;    // Not implemented
   Word mhartid     = 0;

   Reg #(MStatus) rg_mstatus  <- mkReg (mstatus_reset_value);

   MISA             misa        = misa_RISCV_Spec;

   Reg #(MIE)       rg_mie      <- mkRegU;
   Reg #(MTVec)     rg_mtvec    <- mkRegU;


   Reg #(Word)      rg_mscratch <- mkRegU;
   Reg #(Word)      rg_mepc     <- mkRegU;
   Reg #(MCause)    rg_mcause   <- mkRegU;
   Reg #(Word)      rg_mtval    <- mkRegU;
   Reg #(MIP)       rg_mip      <- mkRegU;
`endif

   Reg #(Bit #(64))   rg_mcycle      <- mkReg (0);
   RWire #(Bit #(64)) rw_mcycle      <- mkRWire;
   PulseWire          pw_mcycle_incr <- mkPulseWire;


   Reg #(Bit #(64))   rg_minstret      <- mkReg (0);
   RWire #(Bit #(64)) rw_minstret      <- mkRWire;
   PulseWire          pw_minstret_incr <- mkPulseWire;

`ifdef ISA_PRIV_M
   Reg #(MCounteren) rg_mcounteren <- mkRegU;
`endif

   // ----------------------------------------------------------------
   // Reset.
   // Initialize all GPRs to 0 (not necessary per spec, but useful for debugging)
   // Initialize some CSRs.

   Reg #(RegName) rg_j <- mkRegU;

   rule rl_reset_start (rg_state == RF_RESET_START);
      rg_state    <= RF_RESETTING;

`ifdef ISA_PRIV_M
      rg_mstatus  <= mstatus_reset_value;
      rg_mie      <= word_to_mie (0);
      rg_mtvec    <= word_to_mtvec (mtvec_reset_value);
      rg_mcause   <= word_to_mcause (0);    // Supposed to be the cause of the reset.
      rg_mip      <= word_to_mip (0);
      rg_mcounteren <= mcounteren_reset_value;
`endif

      rg_mcycle   <= 0;
      rw_mcycle.wset (0);
      rw_minstret.wset (0);

      rg_j        <= 1;
   endrule

   rule rl_reset_loop (rg_state == RF_RESETTING);
      regfile.upd (rg_j, 0);
      rg_j <= rg_j + 1;
      if (rg_j == 31)
	 rg_state <= RF_RUNNING;
   endrule

   // ----------------------------------------------------------------
   // CYCLE counter

   rule rl_upd_cycle_incr;
      rg_mcycle <= rg_mcycle + 1;
   endrule

   // ----------------
   // INSTRET

   (* descending_urgency = "rl_reset_start, rl_upd_minstret_csrrx" *)
   rule rl_upd_minstret_csrrx (rw_minstret.wget matches tagged Valid .v);
      rg_minstret <= v;
      // $display ("%0d: Regfiles.rl_upd_minstret_csrrx: new value is %0d", cur_cycle, v);
   endrule

   rule rl_upd_minstret_incr ((! isValid (rw_minstret.wget)) && pw_minstret_incr);
      rg_minstret <= rg_minstret + 1;
      // $display ("%0d: Regfiles.rl_upd_minstret_incr: new value is %0d", cur_cycle, rg_minstret + 1);
   endrule

   // ----------------
   // MCYCLE

   (* descending_urgency = "rl_reset_start, rl_upd_mcycle_csrrx" *)
   rule rl_upd_mcycle_csrrx (rw_mcycle.wget matches tagged Valid .v);
      rg_mcycle <= v;
      // $display ("%0d: Regfiles.rl_upd_mcycle_csrrx: new value is %0d", cur_cycle, v);
   endrule

   rule rl_upd_mcycle_incr ((! isValid (rw_mcycle.wget)) && pw_mcycle_incr);
      rg_mcycle <= rg_mcycle + 1;
      // $display ("%0d: Regfiles.rl_upd_mcycle_incr: new value is %0d", cur_cycle, rg_mcycle + 1);
   endrule

   // ----------------------------------------------------------------

   // ----------------------------------------------------------------
   // Help functions for interface methods
   // TODO: restrict access to certain CSRs in User mode

   // ----------------
   // CSR reads (no side effect)
   // Returns Invalid for invalid CSR addresses or access-mode violations

   function Maybe #(Word) fv_csr_read (CSR_Addr csr_addr);
      Maybe #(Word)  m_csr_value = tagged Invalid;

      case (csr_addr)
	 // User mode csrs
`ifdef ISA_FD
	 // TODO: fixup when we implement FD
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

	 default: m_csr_value = tagged Invalid;
      endcase
      return m_csr_value;
   endfunction
   
   // ----------------
   // CSR writes
   // Returns True if successful
   // If unsuccessful, should trap (illegal CSR).

   function Action fav_write_csr (CSR_Addr csr_addr, Word word);
      action
	 Bool success = True;
	 case (csr_addr)
	    // User mode csrs
`ifdef ISA_FD
	    // TODO: fixup when we implemen FD
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
	    csr_minstret:  rw_minstret.wset ({ rg_minstret [63:32], word });
`ifdef RV32
	    csr_cycleh:    rg_mcycle   <= { word, rg_mcycle   [31:0] };
	    csr_instreth:  rw_minstret.wset ({ word, rg_minstret [31:0] });
`endif

	    default:       success = False;
	 endcase
	 if ((! success) && (cfg_verbosity > 1))
	    $display ("%0d: ERROR: CSR-write addr 0x%0h val 0x%0h not successful", cur_cycle,
		      csr_addr, word);
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

   // CSR read (w.o. side effect)
   method Maybe #(Word) read_csr (CSR_Addr csr_addr);
      return fv_csr_read (csr_addr);
   endmethod

   // CSR read (w. side effect)
   method ActionValue #(Maybe #(Word)) mav_read_csr (CSR_Addr csr_addr);
      return fv_csr_read (csr_addr);
   endmethod

   // CSR write
   method Action write_csr (CSR_Addr csr_addr, Word word);
      fav_write_csr (csr_addr, word);
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

   // Read INSTRET
   method Bit #(64) read_csr_instret;
      return rg_minstret;
   endmethod

   // Increment INSTRET
   method Action csr_instret_incr;
      pw_minstret_incr.send;
   endmethod

   // Read TIME
   method Bit #(64) read_csr_time;
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
      pw_mcycle_incr.send;
   endmethod
endmodule

// ================================================================

endpackage
