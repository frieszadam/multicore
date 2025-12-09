#!/bin/bash

mkdir -p archive_reports
COUNT=$(ls -l archive_reports | wc -l)
cp -r build/syn-rundir/reports archive_reports/syn-report$COUNT
grep "parameter" "v/memsys_top.sv" > archive_reports/syn-report$COUNT/config.txt
grep "set " "cfg/constraints.tcl" >> archive_reports/syn-report$COUNT/config.txt
