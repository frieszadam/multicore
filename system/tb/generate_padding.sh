#!/bin/bash

# Assign arguments to variables for clarity
INPUT_FILE="$1"
OUTPUT_FILENAME="$2"

if [[ -z "$INPUT_FILE" || -z "$OUTPUT_FILENAME" ]]; then
    echo "Usage: $0 <dump_file> <output_filename>"
    exit 1
fi

DATA_ADDR=$(awk '/<input_data>:/ {print $1}' "$INPUT_FILE")
if [[ -z "$DATA_ADDR" ]]; then
    echo "Error: Could not find symbol '<input_data>:' in $INPUT_FILE"
    exit 1
fi

PAD_LINES=$(( (0x$DATA_ADDR - 0x80000000) / 4 ))
echo "Detected .data at 0x$DATA_ADDR. Padding with $PAD_LINES zero lines."

yes "00000000" | head -n "$PAD_LINES" > "tb/$OUTPUT_FILENAME"