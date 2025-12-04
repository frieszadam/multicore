"""
Test Generator
Constructs constrained random directed test sequences including core
input stimulus and expected output results reported by software models.
"""

import sys, re, os
import random, argparse
from collections import deque
from hardware_interface import *
from mem_cache_model import *
sys.path.append('tb/scripts')

WORD_SIZE = 4

def get_cache_params(cache_dir):
    # Extract cache parameters from testbench instantiation
    # Initialize variables to store the extracted values (as strings)
    block_width_p = None
    sets_p = None
    ways_p = None

    # Initialize flags to track if we've found the values
    found_blocks = False
    found_sets = False
    found_ways = False
    found_addr_width = False

    with open(f"{cache_dir}/tb/cache_tb.sv", 'r') as f:
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
            
            if not found_addr_width:
                match_addr_width = re.search(r'localparam mem_addr_width_lp = \s*(\d+)', line)
                if match_addr_width:
                    addr_width_p = int(match_addr_width.group(1)) 
                    found_addr_width = True

            # Exit the loop as soon as all three are found
            if found_blocks and found_sets and found_ways and found_addr_width:
                break

    return (block_width_p, sets_p, ways_p, addr_width_p)
                
def get_random_address(addr_range_start, addr_range_end):
    return random.randrange(addr_range_start, addr_range_end) & ~0b11

def get_random_wdata():
    return random.randrange(0, 2**32)

def get_random_be():
    valid_be = [0b1111, 0b1100, 0b0110, 0b0011, 0b1000, 0b0100, 0b0010, 0b0001, 0b0000]
    return random.choice(valid_be)

def send_command(hardware_interface, mem_model, we, addr, lr_sc, be, wdata):
    hardware_interface.send(we, addr, lr_sc=lr_sc, be=be, wdata=wdata)
    if we == 1:
        hardware_interface.recv(0)
        mem_model.write(addr, wdata, be)
    else:
        rdata = mem_model.read(addr)
        hardware_interface.recv(rdata)

# Sequence of random reads and writes with non-overlapping address ranges for each core
def test_sanity(interfaces, mem_model, mem_limit, **kwargs):
    addr_range_incr = int(mem_limit / num_caches_p)
    lr_sc = 0

    for c, intf in enumerate(interfaces):
        wr_addr_set = set()

        # Ensure that accesses do not overlap
        start = c * addr_range_incr
        end   = (c + 1) * addr_range_incr
        print(f"Core {c} restricted to range: {hex(start)} - {hex(end)}")

        # Simple write and read written value test with distinct address spaces
        for i in range(5000):
            addr = get_random_address(start, end)

            if (random.random() < 0.6):
                # send read
                send_command(intf, mem_model, 0, addr, lr_sc, 0b1111, 0)
            elif (random.random() < 0.9):
                wdata = get_random_wdata()
                be = get_random_be()
                send_command(intf, mem_model, 1, addr, lr_sc, be, wdata)
                wr_addr_set.add(addr)
            else:
                wait_period = random.randrange(10)
                intf.wait(wait_period)
        
        for addr in wr_addr_set:
            send_command(intf, mem_model, 0, addr, lr_sc, 0b1111, 0)

def prune_history(history, global_id, min_dist):
    while history and (global_id - history[0][2] >= min_dist):
        history.popleft()

def is_hazard(history, block_addr, core_id, min_dist, global_id):
    for hist_addr, hist_core, hist_id in history:
        if hist_addr == block_addr:
            # Conflict if: Same Block AND Different Core
            if hist_core != core_id:
                return True
    return False

def verify_memory(interfaces, mem_model, addr_set, wait_cycles):
    # Wait for transactions to settle
    total_wait = wait_cycles * len(interfaces)
    for intf in interfaces:
        intf.wait(total_wait)
        
    # Read back all touched addresses from every core
    for addr in addr_set:
        for intf in interfaces:
            send_command(intf, mem_model, 0, addr, lr_sc, 0b1111, 0)
    
    print(f"Verified {len(addr_set)} unique blocks across {len(interfaces)} cores.")

# Sequence of random reads and writes with overlapping address ranges for each core
# Outlaws writes to the same block within a minimum distance
def test_coherence_random(interfaces, mem_model, mem_limit, **kwargs):
    min_overlap_dist = 25 * len(interfaces)
    num_tests = 100
    
    global_write_id = 0
    write_history = deque() # Stores (block_addr, core_id, write_id)
    wr_addr_set = set()

    for _ in range(num_tests):
        for c, intf in enumerate(interfaces):
            prune_history(write_history, global_write_id, min_overlap_dist)
            
            # Find non-conflicting address
            while True:
                addr = get_random_address(0, mem_limit)
                block_addr = addr & ~(block_width_bytes - 1)
                
                if not is_hazard(write_history, block_addr, c, min_overlap_dist, global_write_id):
                    break

            if random.random() < 0.5:
                send_command(intf, mem_model, 0, addr, lr_sc, 0b1111, 0)
            else:
                wdata = get_random_wdata()
                send_command(intf, mem_model, 1, addr, lr_sc, 0b1111, wdata)
                
                wr_addr_set.add(block_addr)
                write_history.append((block_addr, c, global_write_id))
                global_write_id += 1

    verify_memory(interfaces, mem_model, wr_addr_set, min_overlap_dist)

# Sequence of random reads and writes with overlapping address ranges for each core
# Allows writes to different words of the same block to test false sharing
def test_false_sharing(interfaces, mem_model, mem_limit, **kwargs):
    num_tests = 50
    wr_addr_set = set()

    for _ in range(num_tests):
        # Pick one block for all cores to fight over
        base_addr = get_random_address(0, mem_limit)
        block_addr = base_addr & ~(block_width_bytes - 1)
        wr_addr_set.add(block_addr)

        # Force every core to write to a distinct offset in this block
        for c, intf in enumerate(interfaces):
            # Calculate unique offset per core to avoid data overwrites
            # but ensure block collision
            offset = (c * WORD_SIZE) % block_width_bytes
            addr = block_addr + offset
            
            wdata = get_random_wdata()
            send_command(intf, mem_model, 1, addr, lr_sc, 0b1111, wdata)

    verify_memory(interfaces, mem_model, wr_addr_set, 10)

TEST_REGISTRY = {
    "sanity": test_sanity,
    "coherence": test_coherence_random,
    "false_sharing": test_false_sharing
}

#   main()
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('--test', default="sanity", choices=TEST_REGISTRY.keys())
    parser.add_argument('--seed', type=int, default=42)
    parser.add_argument('--mem_init', default="DMA_INIT.mem")
    parser.add_argument('--num_caches', type=int, default=2)
    parser.add_argument('--verbosity', default=False)
    parser.add_argument('--cache_dir')

    args = parser.parse_args()

    random.seed(args.seed)
    num_caches_p = args.num_caches

    block_width_p, sets_p, ways_p, addr_width_p = get_cache_params(args.cache_dir)
    block_width_bytes = block_width_p * 4
    # cache_size_bytes = block_width_bytes * ways_p * sets_p

    if os.path.isfile(args.mem_init):
        mem_model = MemoryModel.from_file(args.mem_init)
    else:
        mem_model = MemoryModel()
    
    hardware_interface_list = []
    for c in range(num_caches_p):
        intf_name = "core_intf" + str(c)
        hardware_interface_list.append(HardwareInterface(intf_name, verbose=args.verbosity))

    test_func = TEST_REGISTRY[args.test]
    test_func(
        interfaces=hardware_interface_list,
        mem_model=mem_model,
        mem_limit=2**(addr_width_p + 2),
        block_width_bytes=block_width_bytes
    )

    for c in range(num_caches_p):      
        #### DONE ####
        hardware_interface_list[c].wait(10)
        hardware_interface_list[c].done()
