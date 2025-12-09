# GPT GENERATED GIVEN THE FOLLOWING INSTRUCTIONS
# "Create a script to automate the steps 2 through 4 in docs/build_protocol.txt"

import os
import re
import subprocess
import sys
import math

# --- Configuration ---
# Adjust these paths if your file structure differs
MEMSYS_TOP_PATH = "v/memsys_top.sv" 
CFG_YML_PATH = "cfg/cfg.yml"
GENERATED_V_PATH = "build/sram_generator-rundir/generated_v/bsg_mem_1rw_sync_all.v"
FAKERAM_PATH = os.getenv('BSG_ROOT') + "/hard/fakeram/"

def get_verilog_parameter(content, param_name, default=None):
    """
    Extracts a parameter value from Verilog content using regex.
    Handles 'parameter name = value' and 'localparam name = value'.
    """
    # Regex to find 'parameter [type] name = value' or 'localparam [type] name = value'
    # Updated to handle various terminators (comma, semicolon, paren) and types
    pattern = re.compile(
        r"(?:parameter|localparam)\s+.*?\b{}\b\s*=\s*(\d+)".format(param_name),
        re.MULTILINE
    )
    match = pattern.search(content)
    if match:
        return int(match.group(1))
    
    if default is not None:
        print(f"Warning: Parameter '{param_name}' not found. Using default: {default}")
        return default
        
    raise ValueError(f"Could not find parameter '{param_name}' in {MEMSYS_TOP_PATH}")

def step_2_update_cfg(params):
    """
    Reads cfg.yml, updates specific lines based on extracted parameters,
    and writes it back, preserving comments and structure.
    """
    print(f"--- Step 2: Updating {CFG_YML_PATH} ---")
    
    dma_blk_ratio = params['block_width_p'] // params['dma_data_width_p']

    log2_block_width = math.ceil(math.log2(params['block_width_p']))
    log2_sets = math.ceil(math.log2(params['sets_p']))
    tag_width = 32 - (log2_block_width + 2) - log2_sets

    # Calculate target values
    ram_configs = [
        {
            "id": "data",
            "depth": params['sets_p'] * dma_blk_ratio,
            "width": params['dma_data_width_p'] * 32
        },
        {
            "id": "tag",
            "depth": params['sets_p'],
            "width": tag_width
        },
        {
            "id": "state",
            "depth": params['sets_p'],
            "width": params['ways_p'] * params.get('block_state_width_lp')
        }
    ]

    with open(CFG_YML_PATH, 'r') as f:
        lines = f.readlines()

    new_lines = []
    current_ram_idx = -1
    
    # Simple state machine to track which RAM comment we passed last
    # -1: None, 0: Data, 1: Tag, 2: State
    
    for line in lines:
        stripped = line.strip()
        
        # Detect context based on comments in the YAML
        if "# data ram" in stripped:
            current_ram_idx = 0
        elif "# tag ram" in stripped:
            current_ram_idx = 1
        elif "# state ram" in stripped:
            current_ram_idx = 2
            
        # If we are inside a list item definition (starts with {name:)
        if stripped.startswith("{name:") and current_ram_idx != -1:
            config = ram_configs[current_ram_idx]
            depth = config['depth']
            width = config['width']
            name = f"fakeram_d{depth}_w{width}"
            
            # Reconstruct the line strictly preserving format but swapping values
            # We assume the format provided: {name: "...", family: "...", depth: N, width: N, ...}
            
            # Regex to replace specific keys while keeping others intact
            # Replace name
            line = re.sub(r'name:\s*"[^"]+"', f'name: "{name}"', line)
            # Replace depth
            line = re.sub(r'depth:\s*\d+', f'depth: {depth}', line)
            # Replace width
            line = re.sub(r'width:\s*\d+', f'width: {width}', line)
            
            print(f"  Updated {config['id']} ram -> Name: {name}, Depth: {depth}, Width: {width}")
            
            # Reset context so we don't update wrong lines
            current_ram_idx = -1 
            
        new_lines.append(line)

    with open(CFG_YML_PATH, 'w') as f:
        f.writelines(new_lines)
    print("  Config file updated.")

def step_3_make_sram():
    """Run the make command."""
    print("--- Step 3: Running 'make sram' ---")
    try:
        subprocess.run(["make", "sram"], check=True)
        print("  Make completed successfully.")
    except subprocess.CalledProcessError as e:
        print("  Error: 'make sram' failed.")
        sys.exit(1)

def step_4_patch_verilog():
    """
    Modifies the generated Verilog file to fix include paths.
    """
    print(f"--- Step 4: Patching {GENERATED_V_PATH} ---")
    
    if not os.path.exists(GENERATED_V_PATH):
        print(f"  Error: Generated file {GENERATED_V_PATH} not found.")
        sys.exit(1)

    # Calculate absolute path
    abs_base_path = FAKERAM_PATH
    # Ensure path ends with slash for cleaner concatenation
    if not abs_base_path.endswith(os.sep):
        abs_base_path += os.sep

    print(f"  Resolved absolute path base: {abs_base_path}")

    with open(GENERATED_V_PATH, 'r') as f:
        content = f.read()

    # Regex to find `include "something.svh"
    # Capture the filename inside the quotes
    
    def replacer(match):
        basename = match.group(1)
        new_path = os.path.join(abs_base_path, basename)
        return f'`include "{new_path}"'

    # Pattern: `include "(*.svh)"
    pattern = re.compile(r'`include\s+"([^"]+\.svh)"')
    
    new_content, count = pattern.subn(replacer, content)
    
    if count == 0:
        print("  Warning: No include paths matching pattern found to replace.")
    else:
        print(f"  Replaced {count} include directives.")

    with open(GENERATED_V_PATH, 'w') as f:
        f.write(new_content)

def main():
    if not os.path.exists(MEMSYS_TOP_PATH):
        print(f"Error: {MEMSYS_TOP_PATH} not found. Please run this from the project root.")
        sys.exit(1)

    print(f"Reading parameters from {MEMSYS_TOP_PATH}...")
    with open(MEMSYS_TOP_PATH, 'r') as f:
        verilog_content = f.read()

    # Extract required parameters
    params = {
        'sets_p': get_verilog_parameter(verilog_content, 'sets_p'),
        'block_width_p': get_verilog_parameter(verilog_content, 'block_width_p'),
        'dma_data_width_p': get_verilog_parameter(verilog_content, 'dma_data_width_p'),
        'ways_p': get_verilog_parameter(verilog_content, 'ways_p'),
        'block_state_width_lp': 2
    }

    print(f"Extracted Params: {params}")

    step_2_update_cfg(params)
    step_3_make_sram()
    step_4_patch_verilog()
    
    print("\nAutomation complete.")

if __name__ == "__main__":
    main()