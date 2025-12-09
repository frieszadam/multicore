**Parameterized Snooping Cache-Coherent Multiprocessor**

A synthesizable, snooping-based symmetric multiprocessor (SMP) system implemented in SystemVerilog.


Project Overview

This project integrates open-source RISC-V cores with a custom-designed memory subsystem to explore cache coherence scaling
and physical implementation in the Skywater 130nm process node. The MESI protocol is implemeted with Zalrsc support (LR/SC).

*Key Features*

Parameterized Design: Easily modify core counts, cache sizes (sets/ways), and bus widths via top-level parameters.

Non-Blocking Snoops: The cache controller utilizes duplicated state/tag arrays to handle bus snoops without stalling the processor pipeline.

Synthesizable: The design is clean, lint-checked, and ready for logic synthesis, with specific optimizations for the Skywater 130nm node (SRAM macro integration via OpenRAM/Basejump).


*Repository Structure*

src/
- SystemVerilog RTL; including bus, snoop controller

cfg/
- Source file lists, constraints, and configuration used in Hammer

tb/
- Testbench and script infrastructure for verification 

docs/
- Notes about build process and testing.


*Prerequisites*

Simulation: Synopsys VCS.

Synthesis (Optional): Cadence Genus.


*Getting Started*

To run the default coherence stress test (verifying data consistency across cores):

cd memsys
make run_test TESTCASE=coherence NUM_CACHE=2
