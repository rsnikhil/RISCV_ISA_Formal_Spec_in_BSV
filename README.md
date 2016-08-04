# RISCV ISA Formal Spec in BSV
A formal spec of the RISC-V Instruction Set Architecture, written in Bluespec BSV (executable, synthesizable).

MIT License (see LICENSE.txt)

This is a first cut at writing a formal specification of the RISC-V ISA in BSV.  
Text documents describing the ISA may be found at [The RISC-V Foundation](https://riscv.org/).

This first cut only covers RV32I and RV64I user-mode instructions,
plus a few standard machine-mode registers that save exception
information in case of exceptions.  It will be extended in future to
cover other user-level features (M, A, F, D, etc.) and other privilege
levels (machine, supervisor and hypervisor).

This spec is executable, both in simulation and in hardware.
Simulation vehicles include Bluespec Bluesim and Verilog simulators.
Hardware execution would typically be on an FPGA, where it could be
used as a "tandem verifier" for an actual CPU implementation.

In this repo we provide the BSV source codes for the spec itself.  The
source code contains detailed comments.

We also provide a pre-built Bluesim simulation executable, where the
spec has been embedded into a larger "SoC" system involving a memory
system and a UART, so that you can run it on RISC-V ELF executables
compiled for "bare metal" execution (no OS).  We provide a few
pre-built ELF files for this purpose, as examples.  The simulation
executable should run on any 64-bit Linux.

----------------------------------------------------------------

## Repository contents:

* `src_BSV/`

  This is the spec, written in BSV, in the following files:

    * `ISA_Decls.bsv`     Specifies instruction encodings

    * `RISCV_Spec.bsv`    Specifies instruction semantics


* `Bluesim/`

  Contains a pre-built 64-bit Linux executable using Bluespec, Inc.'s
  Bluesim simulator.  The Makefile allows running the simulator on any
  of the pre-compiled ELF files in `RISCV_Programs/` directory.

  For example, `$ make do_test_hello` runs the "Hello World!" program.

* `RISCV_Programs/`

    * `C_tests_RV32IM/`

    * `asm_tests_RV32IM/`

    These contain a number of sub-directories (e.g., "hello/",
    containing a "Hello World!" program).  Each directory contains a
    .c (C) or .S (assembly) source file, a pre-compiled RISC-V RV32IM
    ELF executable, and a .text dis-assembly of the ELF file.

----------------------------------------------------------------
## Running the Bluesim simulator on RISC-V ELF files

You should be in the Bluesim directory: `$ cd Bluesim`

To run an individual program, e.g., "Hello World!": `$ make do_test_hello`

To run all programs (file `sample_transcript` is a transcript of this): `$ make do_tests`

In `sample_transcript` you will see that for two programs, `print` and
`intOpsTest`, execution prints an error message like this:

        RISCV_Spec.fa_do_exception: epc = 0x11fec, exc_code = 0x2, badaddr = 0xaaaaaaaa

This is because those two ELF executables contain the `REMU`
instruction which is not part of the base I instruction set (they are
in the `M` extension), and the spec correctly identifies them as
illegal instructions.

If you set the environment variable SIM_VERBOSITY (to 1, 2, ...) it
will produce increasingly detailed simulation traces indicating
activity on a clock-by-clock basis in the CPU pipeline, caches,
interconnect fabric and memory controller.

Note: The `make` commands invoke the Bluesim executable: `$ exe_d`

If you provide the flag `-V` it will dump VCDs waveforms to the file `dump.vcd`.

If you provide the flag `-V foo.vcd` it will dump VCDs waveforms to the file `foo.vcd`.

----------------------------------------------------------------
## References

Bluespec support: email `support@bluespec.com`

Bluespec, Inc. web site [www.bluespec.com](http://www.bluespec.com).

RISC-V Foundation web site [www.riscv.org](https://riscv.org)

