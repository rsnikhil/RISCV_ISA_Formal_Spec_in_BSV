# Makefile to run pre-packaged test simulations of RISCV_ISA_Formal_Spec_in_BSV
# Please see README.md

# To run a test (e.g., Hello World!):
#    make  test_hello

# Default verbosity is 0
# SIM_VERBOSITY 1 will provide and instruction trace
# SIM_VERBOSITY 2 will provide more detail (try it!)
# Try it like this:
#     make SIM_VERBOSITY=n test_hello

SIM_VERBOSITY ?= 0

.PHONY: test_hello
test_hello:
	ln -s -f  Test_Programs/hello/hello.mem_hex  Mem_Model.hex
	Simulator/exe_hw_d    | tee transcript_hello_verbosity_$(SIM_VERBOSITY)

.PHONY: test_qsort
test_qsort:
	ln -s -f  Test_Programs/qsort/qsort.mem_hex  Mem_Model.hex
	Simulator/exe_hw_d    | tee transcript_qsort_verbosity_$(SIM_VERBOSITY)

.PHONY: test_towers
test_towers:
	ln -s -f  Test_Programs/towers/towers.mem_hex  Mem_Model.hex
	Simulator/exe_hw_d    | tee transcript_towers_verbosity_$(SIM_VERBOSITY)
