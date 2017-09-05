# RISCV ISA Formal Spec in BSV
A formal spec of the RISC-V Instruction Set Architecture, written in Bluespec BSV (executable, synthesizable).

MIT License (see LICENSE.txt)

This is a formal specification, written in BSV, of (a subset of) the
RISC-V ISA.  The original RISC-V specs (written in English text) are
the following two documents at [The RISC-V
Foundation](https://riscv.org/):

>    The RISC-V Instruction Set Manual  
>    Volume I: User-Level ISA  
>    Document Version 2.2  
>    Editors: Andrew Waterman , Krste Asanovic  
>    May 7, 2017


>    The RISC-V Instruction Set Manual  
>    Volume II: Privileged Architecture  
>    Privileged Architecture Version 1.10  
>    Editors: Andrew Waterman , Krste Asanovic  
>    May 7, 2017

This formal spec covers:

   - RV32IM and RV64IM, i.e., the 32-bit and 64-bit user-level
        instruction sets ("I"), including integer
        multiply/ divide/ remainder ("M").

   - A subset of machine-level privileged instructions and CSRs,
        including trap handling but excluding physical memory
        protection and performance-monitoring.

This formal spec will be extended in future to cover other user-level
features (A, F, D, etc.) and other privilege levels (supervisor).

This spec is executable, both in simulation and in hardware.
Simulation vehicles include Bluespec Bluesim and Verilog simulators.
Hardware execution would typically be on an FPGA, where it could be
used as a "tandem verifier" for an actual CPU implementation.

In this repo we provide the BSV source codes for the spec.  The source
code contains detailed comments.

For simulation executables, please contact the author.

----------------------------------------------------------------

## Repository contents:

The specification is in the following BSV files:

`ISA_Decls.bsv`  
&nbsp; &nbsp; &nbsp; Specifies user-level instruction encodings.

`ISA_Decls_Priv_M.bsv`  
&nbsp; &nbsp; &nbsp; Specifies machile-level privilege CSRs and instruction encodings.

`RISCV_Spec.bsv`  
&nbsp; &nbsp; &nbsp; The top-level of the spec, specifying instruction semantics.

`RegFiles.bsv`  
&nbsp; &nbsp; &nbsp; Specifies integer GPRs and CSRs

`IntMulDivRem_ALU.bsv`  
&nbsp; &nbsp; &nbsp; Specifies ALU for "M" operation (Mul/Div/Rem)

In `RISCV_Spec.bsv`, the spec is encapsulated into module
`mkRISCV_Spec` whose parameters include a register file and a memory,
and whose interface includes hooks to control its execution from GDB.
Inside the module the main action is in rules `rl_fetch` and
`rl_exec`.  The latter invokes the top-level semantic function
`fa_exec()`.

We deliberately split LD, ST, FENCE.I and FENCE instructions into two
phases (instead of treating them as pure functions) in order to allow
access to shared memory to be interleaved with other hardware threads.
The second phase of these instructions is seen in the rules
`rl_exec_LD_response`,
`rl_exec_ST_response`
`rl_exec_FENCE_I_response`,
and `rl_exec_FENCE_response`.

----------------------------------------------------------------
## References

Bluespec support: email `support@bluespec.com`

Bluespec, Inc. web site [www.bluespec.com](http://www.bluespec.com).

RISC-V Foundation web site [www.riscv.org](https://riscv.org)
