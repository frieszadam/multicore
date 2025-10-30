# Make file for a Hammer project
TOP_DIR := $(realpath ../ee478-hammer)
OBJ_DIR := build
INPUT_CFGS := cfg/cfg.yml cfg/src.yml
TB_CFGS := cfg/tb.yml

# REVISIT SUBMODULE basejump_stl
BASEJUMP_STL_PATH := $(realpath ../basejump_stl)
include $(TOP_DIR)/module_top.mk
