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
    return random.randrange(0, 2**4)

def send_command(hardware_interface, mem_model, cache_model, we, addr, be, wdata):
    hardware_interface.send(we, addr, be, wdata)
    if we:
        hardware_interface.recv(0, 0)
        mem_model.write(addr, wdata, be)
        cache_model.process_write(addr, wdata, be)
    else:
        rdata = mem_model.read(addr)
        hardware_interface.recv(rdata, 0)
        cache_model.process_read(addr)

#   main()
if __name__ == "__main__":
    # REVISIT memory intialization
    # dma_mem_file = sys.argv[2]
    # update_dma_model_init(True, dma_mem_file)
    # dma_mem = DMA_Mem(dma_mem_file)

    seed = int(sys.argv[1])  
    print("Using command-line input seed {}".format(seed))
    random.seed(seed)

    block_size_bytes = block_width_p * 4
    cache_size_bytes = block_size_bytes * ways_p * sets_p

    mem_model = MemoryModel()
    cache_model = CacheModel(cache_size_bytes, block_size_bytes, ways_p)
    hardware_interface = HardwareInterface("core_intf")

    # Simple write and read written value test
    for i in range(500):
        addr = get_random_address()
        wdata = get_random_wdata()

        # Write random data to random address
        send_command(hardware_interface, mem_model, cache_model, 1, addr, 0b1111, wdata)

        # Read newly written data
        send_command(hardware_interface, mem_model, cache_model, 0, addr, 0b1111, wdata)

    full_set_indices = cache_model.get_full_sets()
    addr_queue = []
    for set_index in full_set_indices:
        # Cause evictions in full sets
        we = 0
        rdata = 0
        wdata = 0
        be = 0b1111

        if random.random() < 0.7:
            rdata = mem_model.read(addr)
        else:
            we = 1
            wdata = get_random_wdata()

        addr = get_random_address_set(set_index)
        addr_queue.append(addr)

        send_command(hardware_interface, mem_model, cache_model, we, addr, 0b1111, wdata)
        # hardware_interface.send(we, addr, 0b1111, wdata)
        # hardware_interface.recv(rdata, 0)
        
    for addr in addr_queue:
        for i in range(block_width_p >> 2):
            # Read from loaded blocks
            addr += i << 2
            send_command(hardware_interface, mem_model, cache_model, 0, addr, 0b1111, 0)
            hardware_interface.send(0, addr)
            rdata = mem_model.read(addr)
            hardware_interface.recv(rdata, 0)
            
    #### DONE ####
    hardware_interface.wait(10)
    hardware_interface.done()
