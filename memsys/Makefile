# Make file for a Hammer project
TOP_DIR := $(realpath ../../ee477-hammer-cad)
OBJ_DIR := build
INPUT_CFGS := cfg/cfg.yml cfg/src.yml
TB_CFGS := cfg/tb.yml

# REVISIT SUBMODULE basejump_stl
BASEJUMP_STL_PATH := $(realpath ../basejump_stl)
include $(TOP_DIR)/module_top.mk
export BSG_ROOT = $(BASEJUMP_STL_PATH)

CORE_TRACE_FILE = tb/core_intf
CORE_TRACE_ROM = bsg_core_intf_trace_rom
CORE_TRACE_ROM_V = tb/bsg_core_intf_trace_rom

# default DMA memory
DMA_MEM ?= "dma_init.hex"
CACHE_DIR = $(abspath .)
SEED ?= "123"
VERBOSE ?= "False"
NUM_CACHE ?= 2
TEST ?= "sanity"

gen_dma_init:
	CACHE_DIR=$(CACHE_DIR) python3 tb/scripts/gen_dma_init.py $(SEED)

# make gen_rom TEST=<TEST> NUM_CACHE=<NUM_CACHE> SEED=<SEED> DMA_MEM=<DMA_MEM> VERBOSE=<VERBOSITY_ON>
gen_rom:
	python3 tb/scripts/test_generator.py --seed $(SEED) --cache_dir $(CACHE_DIR) --test $(TEST) --mem_init $(CACHE_DIR)/tb/$(DMA_MEM) --num_cache $(NUM_CACHE) --verbosity $(VERBOSE); \
	for ((i = 0; i <$(NUM_CACHE); i++)); do \
		python3 $(BASEJUMP_STL_PATH)/bsg_mem/bsg_ascii_to_rom.py $(CORE_TRACE_FILE)$$i.tr $(CORE_TRACE_ROM)$$i \
		> $(CORE_TRACE_ROM_V)$$i.v; \
	done

run_test: gen_rom sim-rtl

gen_sram:
	python3 generate_sram.py