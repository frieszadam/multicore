import sys, re, random, os

cache_directory = os.environ.get('CACHE_DIR')

def get_addr_width():
    # Extract address width from testbench instantiation
    # Initialize variables to store the extracted values (as strings)
    mem_addr_width_p = None

    with open(f"{cache_directory}/tb/cache_tb.sv", 'r') as f:
        for line in f:
            match_addr = re.search(r'localparam mem_addr_width_lp = \s*(\d+)', line)
            if match_addr:
                mem_addr_width_p = int(match_addr.group(1)) 
                break
    return mem_addr_width_p

if __name__ == "__main__":
    seed = int(sys.argv[1])  
    print(f"dma_init.mem @ {cache_directory}/tb/ | SEED = {seed}")
    random.seed(seed)
    
    mem_addr_width_p = get_addr_width()
    if (mem_addr_width_p is None):
        print("Error: Memory address assignment in TB not recognized.")
        sys.exit(1)
    
    with open(f"{cache_directory}/tb/dma_init.mem", 'w') as f:
        for addr in range(2 ** mem_addr_width_p):
            rand_word = random.randint(0, 2**32 - 1)
            f.write(f"{rand_word:08x}\n")
