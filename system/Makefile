# Make file for a Hammer project
TOP_DIR := $(realpath ../../ee477-hammer-cad)
OBJ_DIR := build
INPUT_CFGS := cfg/cfg.yml cfg/src.yml
TB_CFGS := cfg/tb.yml

# REVISIT SUBMODULE basejump_stl
BASEJUMP_STL_PATH := $(realpath ../basejump_stl)
CV32E40X_PATH := $(realpath ../cv32e40x)
include $(TOP_DIR)/module_top.mk
export BSG_ROOT = $(BASEJUMP_STL_PATH)
export CV32E40X_ROOT = $(CV32E40X_PATH)

# --- Configuration Variables ---
XLEN ?= 32

# Path to the pre-built ELF file (your initial input)
ELF_FILE := program.riscv 

# Compiler and tool prefixes
RISCV_TOOLCHAIN_PREFIX := riscv$(XLEN)-unknown-elf

OBJCOPY := $(RISCV_TOOLCHAIN_PREFIX)-objcopy

# Target names
IMEM_HEX := instruction_memory.hex
DMEM_HEX := data_memory.hex
ELF_FILE := ../riscv-tests/benchmarks/$(BMARK).riscv
# --- Main Build Targets ---

.PHONY: all clean

gen_pmem: $(IMEM_HEX) $(DMEM_HEX)

# Generate Instruction Memory Hex File (Code)
# This extracts ALL code sections (e.g., .text.init, .text)
$(IMEM_HEX): $(ELF_FILE)
	@echo "OBJCOPY -> IMEM: $@"
	$(OBJCOPY) -O binary --only-section=.text.init --only-section=.text --only-section=.text.startup $(ELF_FILE) $@.code.bin
	xxd -e -c 4 $@.code.bin | cut -d' ' -f2 > tb/$@
	@rm $@.code.bin

# Generate Data Memory Hex File (Initialized Data)
$(DMEM_HEX): $(ELF_FILE)
	@echo "OBJCOPY -> DMEM: $@"
	$(OBJCOPY) -O binary --only-section=.data --only-section=.sdata $(ELF_FILE) $@.data.bin
	./tb/generate_padding.sh $(ELF_FILE).dump $@
	xxd -e -c 4 $@.data.bin | cut -d' ' -f2 >> tb/$@
	rm $@.data.bin

awk_test:
	DATA_ADDR=$$("echo '0'")
	echo $(DATA_ADDR)
# --- Cleanup ---

clean:
	@rm -f *.o *.elf *.bin *.hex