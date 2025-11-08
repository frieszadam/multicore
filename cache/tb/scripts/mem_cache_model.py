"""
Cache and Memory Software Models
Used to predict expected results, including read data and
memory requests from the cache.
"""

import re
from hardware_interface import *
import math

class MemoryModel:
    """A byte-addressable model for main memory."""
    def __init__(self, size_words=2**14, initial_data=None):
        if initial_data:
            self.memory = initial_data
            self.size_bytes = len(initial_data)
            print("Initialized memory model from file.")
        else:
            self.memory = [0 for _ in range(size_words)]
            self.size_bytes = size_words * 4
            print("Initialized memory model with all 0s.")

        print(f"Byte elements: {self.size_bytes} (Size: {self.size_bytes / 1024:.2f} KB)")
    
    @classmethod
    def from_file(cls, filepath):
        """
        Class method to create a MemoryModel from a file.
        The file must contain one 32-bit hexadecimal word per line.
        These words are stored in memory as little-endian bytes.
        """
        if not os.path.exists(filepath):
            raise FileNotFoundError(f"Memory file not found at: {filepath}")

        initial_data_bytes = []
        try:
            with open(filepath, 'r') as f:
                for line in f:
                    # Remove whitespace and skip empty lines
                    line = line.strip()
                    if not line:
                        continue
                        
                    # Parse the 32-bit word
                    word = int(line, 16)
                    
                    # Convert the word to 4 bytes in little-endian order
                    byte0 = (word >> 0) & 0xFF
                    byte1 = (word >> 8) & 0xFF
                    byte2 = (word >> 16) & 0xFF
                    byte3 = (word >> 24) & 0xFF
                    
                    # Add the bytes to our memory list
                    initial_data_bytes.extend([byte0, byte1, byte2, byte3])
                    
        except Exception as e:
            print(f"Error reading file '{filepath}': {e}")
            return cls() # return empty model

        # Create a new class instance with the loaded byte data
        return cls(initial_data=initial_data_bytes)

    def read(self, address):
        """Reads a 32-bit word from a given address."""
        base_addr = address & ~0b11 # Align to word boundary
        if (base_addr + 3) >= self.size_bytes:
            print(f"WARN: Memory read out of bounds at address {hex(address)} (aligned to {hex(base_addr)})")
            return 0

        byte0 = self.memory[base_addr + 0]
        byte1 = self.memory[base_addr + 1]
        byte2 = self.memory[base_addr + 2]
        byte3 = self.memory[base_addr + 3]
        
        word = (byte3 << 24) | (byte2 << 16) | (byte1 << 8) | byte0
        return word

    def write(self, address, data, byte_enable=0b1111):
        """Writes up to a 32-bit word to a given address based on byte_enable."""
        base_addr = address & ~0b11 # Align to word boundary
        if (base_addr + 3) >= self.size_bytes:
            print(f"WARN: Memory write out of bounds at address {hex(address)} (aligned to {hex(base_addr)})")
            return

        if (byte_enable >> 0) & 1: self.memory[base_addr + 0] = (data >> 0) & 0xFF
        if (byte_enable >> 1) & 1: self.memory[base_addr + 1] = (data >> 8) & 0xFF
        if (byte_enable >> 2) & 1: self.memory[base_addr + 2] = (data >> 16) & 0xFF
        if (byte_enable >> 3) & 1: self.memory[base_addr + 3] = (data >> 24) & 0xFF
