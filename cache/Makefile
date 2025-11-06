# Make file for a Hammer project
TOP_DIR := $(realpath ../../ee478-hammer)
OBJ_DIR := build
INPUT_CFGS := cfg/cfg.yml cfg/src.yml
TB_CFGS := cfg/tb.yml

# REVISIT SUBMODULE basejump_stl
BASEJUMP_STL_PATH := $(realpath ../../basejump_stl)
include $(TOP_DIR)/module_top.mk
export BSG_ROOT=$BASEJUMP_STL_PATH

CORE_TRACE_FILE = tb/core_intf.tr
CORE_TRACE_ROM = bsg_core_intf_trace_rom
CORE_TRACE_ROM_V = tb/bsg_core_intf_trace_rom.v

# default DMA memory
DMA_MEM ?= ""
CACHE_DIR = $(abspath .)
SEED ?= "123"

# make gen_rom SEED=<SEED> DMA_MEM=<DMA_MEM>
gen_rom:
	CACHE_DIR=$(CACHE_DIR) python3 tb/scripts/test_generator.py $(SEED) $(CACHE_DIR)/tb/$(DMA_MEM); \
	python3 $(BASEJUMP_STL_PATH)/bsg_mem/bsg_ascii_to_rom.py $(CORE_TRACE_FILE) $(CORE_TRACE_ROM) \
	> $(CORE_TRACE_ROM_V);

run_test: gen_rom sim-rtl