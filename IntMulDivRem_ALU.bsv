// Copyright (c) 2016-2017 Bluespec, Inc.  All Rights Reserved.

// This is reference combinational reference implementation of Integer
// Multiply/Divide/Remainder, used for specification purposes only.

package IntMulDivRem_ALU;

// ================================================================
// BSV project imports

import ISA_Decls :: *;    // Instruction encodings

// ================================================================

interface IntMulDivRem_ALU_IFC;
   method ActionValue #(Word) m_MUL    (Word v_rs1, Word v_rs2);
   method ActionValue #(Word) m_MULH   (Word v_rs1, Word v_rs2);
   method ActionValue #(Word) m_MULHU  (Word v_rs1, Word v_rs2);
   method ActionValue #(Word) m_MULHSU (Word v_rs1, Word v_rs2);

   method ActionValue #(Word) m_DIV    (Word v_rs1, Word v_rs2);
   method ActionValue #(Word) m_DIVU   (Word v_rs1, Word v_rs2);

   method ActionValue #(Word) m_REM    (Word v_rs1, Word v_rs2);
   method ActionValue #(Word) m_REMU   (Word v_rs1, Word v_rs2);

   // 32b ops in RV64
   method ActionValue #(Word) m_MULW   (Word v_rs1, Word v_rs2);
   method ActionValue #(Word) m_DIVW   (Word v_rs1, Word v_rs2);
   method ActionValue #(Word) m_DIVUW  (Word v_rs1, Word v_rs2);
   method ActionValue #(Word) m_REMW   (Word v_rs1, Word v_rs2);
   method ActionValue #(Word) m_REMUW  (Word v_rs1, Word v_rs2);
endinterface

(* synthesize *)
module mkIntMulDivRem_ALU (IntMulDivRem_ALU_IFC);
   method ActionValue #(Word) m_MUL    (Word v_rs1, Word v_rs2);
      actionvalue
	 // Signed versions of v_rs1 and v_rs2
	 Word_S s_v_rs1 = unpack (v_rs1);
	 Word_S s_v_rs2 = unpack (v_rs2);

	 Word v_rd = pack (s_v_rs1 * s_v_rs2);
	 return v_rd;
      endactionvalue
   endmethod

   method ActionValue #(Word) m_MULH   (Word v_rs1, Word v_rs2);
      actionvalue
	 // Signed versions of v_rs1 and v_rs2
	 Word_S s_v_rs1 = unpack (v_rs1);
	 Word_S s_v_rs2 = unpack (v_rs2);

	 Int #(XLEN_2) s_v1     = extend (s_v_rs1);
	 Int #(XLEN_2) s_v2     = extend (s_v_rs2);
	 Int #(XLEN_2) s_result = s_v1 * s_v2;
	 Word v_rd = pack (s_result) [2 * xlen - 1: xlen];
	 return v_rd;
      endactionvalue
   endmethod

   method ActionValue #(Word) m_MULHU  (Word v_rs1, Word v_rs2);
      actionvalue
	 Bit #(XLEN_2) v1     = extend (v_rs1);
	 Bit #(XLEN_2) v2     = extend (v_rs2);
	 Bit #(XLEN_2) result = v1 * v2;
	 Word v_rd = result [2 * xlen - 1: xlen];
	 return v_rd;
      endactionvalue
   endmethod

   method ActionValue #(Word) m_MULHSU (Word v_rs1, Word v_rs2);
      actionvalue
	 // Signed version of v_rs1
	 Word_S s_v_rs1 = unpack (v_rs1);

	 Int #(XLEN_2) s_v1     = extend (s_v_rs1);
	 Int #(XLEN_2) s_v2     = unpack (extend (v_rs2));
	 Int #(XLEN_2) s_result = s_v1 * s_v2;
	 Word v_rd = pack (s_result) [2 * xlen - 1: xlen];
	 return v_rd;
      endactionvalue
   endmethod

   method ActionValue #(Word) m_DIV (Word v_rs1, Word v_rs2);
      actionvalue
	 // Signed versions of v_rs1 and v_rs2
	 Word_S s_v_rs1 = unpack (v_rs1);
	 Word_S s_v_rs2 = unpack (v_rs2);
	 Word v_rd;

	 // Divide by 0; result defined as -1
	 if (v_rs2 == 0)
	    v_rd = '1;

	 // Overflow; result defined as s_v_rs1
	 else if ((v_rs1 == {1'b1, 0}) && (s_v_rs2 == -1))
	    v_rd = v_rs1;

	 else
	    v_rd = pack (s_v_rs1 / s_v_rs2);

	 return v_rd;
      endactionvalue
   endmethod

   method ActionValue #(Word) m_DIVU (Word v_rs1, Word v_rs2);
      actionvalue
	 Word v_rd;

	 // Divide by 0; result defined as all ones
	 if (v_rs2 == 0)
	    v_rd = '1;

	 else
	    v_rd = v_rs1 / v_rs2;

	 return v_rd;
      endactionvalue
   endmethod

   method ActionValue #(Word) m_REM  (Word v_rs1, Word v_rs2);
      actionvalue
	 // Signed versions of v_rs1 and v_rs2
	 Word_S s_v_rs1 = unpack (v_rs1);
	 Word_S s_v_rs2 = unpack (v_rs2);
	 Word v_rd;

	 // Divide by 0; result defined as s_v_rs1
	 if (v_rs2 == 0)
	    v_rd = v_rs1;

	 // Overflow; result defined as 0
	 else if ((v_rs1 == {1'b1, 0}) && (s_v_rs2 == -1))
	    v_rd = 0;

	 else
	    v_rd = pack (s_v_rs1 % s_v_rs2);

	 return v_rd;
      endactionvalue
   endmethod

   method ActionValue #(Word) m_REMU (Word v_rs1, Word v_rs2);
      actionvalue
	 Word v_rd;

	 // Divide by 0; result defined as v_rs1
	 if (v_rs2 == 0)
	    v_rd = v_rs1;

	 else
	    v_rd = v_rs1 % v_rs2;

	 return v_rd;
      endactionvalue
   endmethod

   // ----------------------------------------------------------------
   // 32b ops in RV64

   method ActionValue #(Word) m_MULW   (Word v_rs1, Word v_rs2);
      actionvalue
	 Int #(32) s_v_rs1_32 = unpack (v_rs1 [31:0]);
	 Int #(32) s_v_rs2_32 = unpack (v_rs2 [31:0]);
	 Int #(32) s_v_rd_32  = (s_v_rs1_32 * s_v_rs2_32);
	 Word v_rd = pack (signExtend (s_v_rd_32));
	 return v_rd;
      endactionvalue
   endmethod

   method ActionValue #(Word) m_DIVW   (Word v_rs1, Word v_rs2);
      actionvalue
	 Int #(32) s_v_rs1_32 = unpack (v_rs1 [31:0]);
	 Int #(32) s_v_rs2_32 = unpack (v_rs2 [31:0]);
	 Word v_rd;

	 // Divide by 0; result defined as -1
	 if (v_rs2 == 0)
	    v_rd = '1;

	 // Overflow; result defined as s_v_rs1
	 else if ((v_rs1 == {1'b1, 0}) && (s_v_rs2_32 == -1))
	    v_rd = pack (signExtend (s_v_rs1_32));

	 else
	    v_rd = pack (signExtend ((s_v_rs1_32 / s_v_rs2_32)));

	 return v_rd;
      endactionvalue
   endmethod

   method ActionValue #(Word) m_DIVUW  (Word v_rs1, Word v_rs2);
      actionvalue
	 Bit #(32) v_rs1_32 = v_rs1 [31:0];
	 Bit #(32) v_rs2_32 = v_rs2 [31:0];
	 Word v_rd;

	 // Divide by 0; result defined as all ones
	 if (v_rs2_32 == 0)
	    v_rd = '1;

	 else
	    v_rd = signExtend (v_rs1_32 / v_rs2_32);

	 return v_rd;
      endactionvalue
   endmethod

   method ActionValue #(Word) m_REMW   (Word v_rs1, Word v_rs2);
      actionvalue
	 Int #(32) s_v_rs1_32 = unpack (v_rs1 [31:0]);
	 Int #(32) s_v_rs2_32 = unpack (v_rs2 [31:0]);
	 Word v_rd;

	 // Divide by 0; result defined as s_v_rs1
	 if (s_v_rs2_32 == 0)
	    v_rd = v_rs1;

	 // Overflow; result defined as 0
	 else if ((pack (s_v_rs1_32) == {1'b1, 0}) && (s_v_rs2_32 == -1))
	    v_rd = 0;

	 else
	    v_rd = pack (s_v_rs1_32 % s_v_rs2_32);

	 return v_rd;
      endactionvalue
   endmethod

   method ActionValue #(Word) m_REMUW  (Word v_rs1, Word v_rs2);
      actionvalue
	 Bit #(32) v_rs1_32 = v_rs1 [31:0];
	 Bit #(32) v_rs2_32 = v_rs2 [31:0];
	 Word v_rd;

	 // Divide by 0; result defined as v_rs1
	 if (v_rs2_32 == 0)
	    v_rd = v_rs1;

	 else
	    v_rd = signExtend (v_rs1_32 % v_rs2_32);

	 return v_rd;
      endactionvalue
   endmethod

endmodule

// ================================================================

endpackage
