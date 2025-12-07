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
