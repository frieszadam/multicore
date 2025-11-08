"""
Test Generator
Constructs constrained random directed test sequences including core
input stimulus and expected output results reported by software models.
"""

import sys, re, os
import random, math
from hardware_interface import *
from mem_cache_model import *
sys.path.append('tb/scripts')

# Constrain addresses for more interesting interactions
addr_range_start = 0x1000
addr_range_end = 0x2000

total_address_bits = 32
cache_directory = os.environ.get('CACHE_DIR')

def get_cache_params():
    # Extract cache parameters from testbench instantiation
    # Initialize variables to store the extracted values (as strings)
    block_width_p = None
    sets_p = None
    ways_p = None

    # Initialize flags to track if we've found the values
    found_blocks = False
    found_sets = False
    found_ways = False

    with open(f"{cache_directory}/tb/cache_tb.sv", 'r') as f:
        for line in f:
            if not found_blocks:
                match_blocks = re.search(r'localparam block_width_lp = \s*(\d+)', line)
                if match_blocks:
                    block_width_p = int(match_blocks.group(1)) 
                    found_blocks = True
            
            if not found_sets:
                match_sets = re.search(r'localparam sets_lp = \s*(\d+)', line)
                if match_sets:
                    sets_p = int(match_sets.group(1))
                    found_sets = True
            
            if not found_ways:
                match_ways = re.search(r'localparam ways_lp = \s*(\d+)', line)
                if match_ways:
                    ways_p = int(match_ways.group(1)) 
                    found_ways = True
            
            # Exit the loop as soon as all three are found
            if found_blocks and found_sets and found_ways:
                break

    return (block_width_p, sets_p, ways_p)
                
def get_random_address():
    return random.randrange(addr_range_start, addr_range_end) & ~0b11

def get_random_address_set(set_index):
    """
    Generates a random 32-bit address that maps to the specified set_index.
    """
    
    offset_bits = math.ceil(math.log2(block_width_p))    
    random_addr = random.getrandbits(total_address_bits)

    clear_mask = ~((1 << sets_p) - 1) << block_width_p
    cleared_addr = random_addr & clear_mask
    final_addr = cleared_addr | (set_index << offset_bits)
    
    return final_addr

def get_random_wdata():
    return random.randrange(0, 2**32)

def get_random_be():
    valid_be = [0b1111, 0b1100, 0b0110, 0b0011, 0b1000, 0b0100, 0b0010, 0b0001, 0b0000]
    rand_index = random.randrange(0, len(valid_be))
    return valid_be[rand_index]

def send_command(hardware_interface, mem_model, we, addr, be, wdata):
    hardware_interface.send(we, addr, be, wdata)
    if we == 1:
        hardware_interface.recv(0)
        mem_model.write(addr, wdata, be)
    else:
        rdata = mem_model.read(addr)
        hardware_interface.recv(rdata)

#   main()
if __name__ == "__main__":
    seed = int(sys.argv[1])  
    print("Using command-line input seed {}".format(seed))
    random.seed(seed)

    dma_mem_file = sys.argv[2]
    verbosity_on = sys.argv[3]

    block_width_p, sets_p, ways_p = get_cache_params()
    block_size_bytes = block_width_p * 4
    cache_size_bytes = block_size_bytes * ways_p * sets_p

    if os.path.isfile(dma_mem_file):
        mem_model = MemoryModel.from_file(dma_mem_file)
    else:
        mem_model = MemoryModel()
    hardware_interface = HardwareInterface("core_intf", verbose=verbosity_on)

    send_command(hardware_interface, mem_model, 0, 0, 0b1111, 0)

    wr_addr_list = []    
    # Simple write and read written value test
    for i in range(5000):
        addr = get_random_address()
        if (random.random() < 0.7):
            send_command(hardware_interface, mem_model, 0, addr, 0b1111, 0)
        else:
            wdata = get_random_wdata()
            be = get_random_be()
            send_command(hardware_interface, mem_model, 1, addr, be, wdata)
            wr_addr_list.append(addr)
    
    for addr in wr_addr_list:
        send_command(hardware_interface, mem_model, 0, addr, 0b1111, 0)
            
    #### DONE ####
    hardware_interface.wait(10)
    hardware_interface.done()
