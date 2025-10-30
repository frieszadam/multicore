"""
Test Generator
Constructs constrained random directed test sequences including core
input stimulus and expected output results reported by software models.
"""

import sys
sys.path.append('tb/scripts')
from hardware_interface import *
from mem_cache_model import *
import random

# Constrain addresses for more interesting interactions
addr_range_start = 0x1000
addr_range_end = 0x2000

def get_random_address():
    return random.randrange(addr_range_start, addr_range_end) & ~0b11

def get_random_wdata():
    return random.randrange(0, 2**32)

def get_random_be():
    return random.randrange(0, 2**4)

#   main()
if __name__ == "__main__":
    # REVISIT memory intialization
    # dma_mem_file = sys.argv[2]
    # update_dma_model_init(True, dma_mem_file)
    # dma_mem = DMA_Mem(dma_mem_file)

    seed = int(sys.argv[1])  
    print("Using command-line input seed {}".format(seed))
    random.seed(seed)

    # REVISIT link to TB instatiation 
    block_size_p = 16
    sets_p = 16
    ways_p = 2

    block_size_bytes = block_size_p * 4
    cache_size_bytes = block_size_bytes * ways_p * sets_p

    mem_model = MemoryModel()
    cache_model = CacheModel(cache_size_bytes, block_size_bytes, ways_p)
    hardware_interface = HardwareInterface("core_intf")

    # Simple write and read written value test
    for i in range(5):
        addr = get_random_address()
        wdata = get_random_wdata()

        # Write random data to random address
        hardware_interface.send(1, addr, 0b1111, wdata)
        hardware_interface.recv(0, 0)
        mem_model.write(addr, wdata)

        # Read newly written data
        hardware_interface.send(0, addr)
        hardware_interface.recv(wdata, 0)

    # for i in range(100):
    #     if random.random() < 0.7:
    #         we = 0
    #         addr = get_random_address()
    #         rdata = mem_model.read(addr)
    #         hardware_interface.send(we, addr)
    #         hardware_interface.recv(rdata, 0)
    #     else:
    #         we = 1
    #         addr = get_random_address()
    #         wdata = get_random_wdata()
    #         be = get_random_be()
    #         mem_model.write(addr, wdata)
    #         hardware_interface.send(we, addr, be, wdata)
    #         hardware_interface.recv(0, 0)

    #### DONE ####
    hardware_interface.wait(10)
    hardware_interface.done()
