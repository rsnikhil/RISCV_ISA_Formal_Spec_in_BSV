ELF_FILE = hello
MEM_HEX_FILE = hello.mem_hex

CC = gcc

.PHONY: default
default: elf_to_hex

elf_to_hex: elf_to_hex.c
	gcc -g  -o elf_to_hex  elf_to_hex.c  -lelf

.PHONY: test
test: elf_to_hex
	./elf_to_hex  $(ELF_FILE)  $(MEM_HEX_FILE)
