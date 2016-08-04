# RISCV_ISA_Formal_Spec_in_BSV
A formal spec of the RISC-V Instruction Set Architecture, written in Bluespec BSV (executable, synthesizable)

This is a first cut at writing a formal specification of the RISC-V ISA in BSV.  
Text documents describing the ISA may be found at [The RISC-V Foundation](https://riscv.org/).

This first cut only covers RV32I and RV64I user-mode instructions, plus a few standard machine-mode registers that save exception information in case of exceptions.  It will be extended in future to cover other privilege levels.

This spec is executable, both in simulation and in hardware.  Simulation vehicles include Bluespec Bluesim and Verilog simulators.  Hardware execution would typically be on an FPGA, where it could be used as a "tandem verifier" for an actual CPU implementation.

In this repo we provide the BSV source codes for the spec itself.  The source code contains detailed comments.

We also provide a pre-built Bluesim simulation executable, where the spec has been embedded into a larger "SoC" system involving a memory system and a UART, so that you can run it on RISC-V ELF executables compiled for "bare metal" execution (no OS).  We provide a few pre-built ELF files for this purpose, as examples.  The simulation executable should run on any 64-bit Linux.
