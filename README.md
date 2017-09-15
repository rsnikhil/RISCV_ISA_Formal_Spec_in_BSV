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

----------------------------------------------------------------

## Source codes

The spec source code files are in the RISCV_Spec/ directory.  The
source code contains detailed comments.

`ISA_Decls.bsv`  
&nbsp; &nbsp; &nbsp; Specifies user-level instruction encodings.

`ISA_Decls_Priv_M.bsv`  
&nbsp; &nbsp; &nbsp; Specifies machine-level privilege CSRs and instruction encodings.

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
## Executability

This spec is executable, both in simulation and in hardware.
Simulation vehicles include Bluespec Bluesim and Verilog simulators.
Hardware execution would typically be on an FPGA, where it could be
used as a "tandem verifier" for an actual CPU implementation.

In this repo we provide a pre-built executable simulator:

>    `Simulator/exe_hw_d`

In this executable:

>    The CPU connects to an I-Cache and a D-Cache  
>    The caches connect to an AXI4-like fabric  
>    The AXI4-like fabric connects to a Memory and a UART
>    (stdio of a program running on the CPU is directed to the UART)

To avoid overwhelming the reader, we do not provide all this extra
infrastructure (which is quite substantial, including a Debug Module
that can connect to GDB, and more). The `RISCV_Spec/` directory only
contains the code for the CPU, and therefore you will not be able to
re-build the excutable.

----------------------------------------------------------------
## Running the executable on example C programs

We have provided a number of example C programs, and their
pre-compiled ELF files etc in directories like these:

>    `Test_Programs/hello`     &nbsp; &nbsp; &nbsp;    (Hello World!)  
>    `Test_Programs/qsort`     &nbsp; &nbsp; &nbsp;    (Quicksort)  
>    `Test_Programs/towers`    &nbsp; &nbsp; &nbsp;    (Towers of Hanoi)  

Each directory contains a number of files.  For example, in the
`hello` directory you will see:

>    `hello.c`

This is the orginal C source code.

>    `hello`

This is an ELF file, produced by using gcc to compile the C program
for a bare-metal RISC-V RV32IM target (i.e., not Linux target).  To
recreate an ELF file you will have to build yourself a RISC-V Gnu tool
chain.  Our bare-metal ELF files have startup code that start
execution at PC = 0x200, and connect stdio to the UART.

>    `hello.text`

A text disassembly of the ELF program using the standard `objdump` Gnu
tool (part of the RISC-V Gnu tool chain).

>    `hello.mem_hex`

A memory contents file produced from the ELF file.  This is in
standard Verilog 'Memory Hex' format, and represents the contents of
memory when the RISC-V CPU starts executing.  See section below on
ELF-to-hex conversion.

To run an example program, in the top-level directory you can say:

>    `make test_hello`  
>    `make test_qsort`  
>    `make test_towers`  

As you will see from the simple Makefile in the top-level directory,
it makes a symbolic link from `Mem_Model.hex` to one of the test
program memhex files, and then runs `Simlator/exe_hw_d`.

The output is more interesting if you turn on simulation verbosity:

>    `make  SIM_VERBOSITY=1  test_hello`  &nbsp; &nbsp; &nbsp;    PC and instruction trace  
>    `make  SIM_VERBOSITY=2  test_hello`  &nbsp; &nbsp; &nbsp;    More detail  

In each test program directory you will see transcripts of running the
program at various verbosity levels:

>    `transcript_hello_verbosity_0`    
>    `transcript_hello_verbosity_1`    
>    `transcript_hello_verbosity_2`    

If you have a RISC-V toolchain, you can compile your own C program
into an ELF file, convert it into a memhex file, and run the simulator
on it.  Please contact us for details of the boilerplate code to start
execution at PC 0x200 and to connect stdio to the UART.

----------------------------------------------------------------

## ELF to Mem Hex file conversion

Many ELF-to-hex tools exist on the Web, but we have also provided a
simple one in:

>    `Tool_elf_to_hex/elf_to_hex.c`

Compile this file, and then execute it with two command-line
arguments, the path/filename of the input ELF file, and the
path/filename of the output memhex file.

----------------------------------------------------------------
## References

Bluespec support: email `support@bluespec.com`

Bluespec, Inc. web site [www.bluespec.com](http://www.bluespec.com).

RISC-V Foundation web site [www.riscv.org](https://riscv.org)
