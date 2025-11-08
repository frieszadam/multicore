"""
Hardware Interface
Convert read and write commands into physical trace/bit-stream
expected by hardware modules.
Adapted from code by Katherine Bergey circa EE526
"""

import os

class HardwareInterface:

  # constructor
  def __init__(self, interface_name, verbose=False):
    self.addr_width_p = 32
    self.data_width_p = 32
    self.byte_enable_width_p = 4
    self.send_data_len = self.addr_width_p + self.data_width_p + 1 + self.byte_enable_width_p
    self.receive_data_len = self.data_width_p
    self.packet_len =  max(self.send_data_len, self.receive_data_len)
    self.verbose = verbose

    out_dir = "tb"
    if not os.path.exists(out_dir):
      print("Error: could not find path to tb directory")
    self.fwrite = open(os.path.join(out_dir, interface_name + ".tr"), "w")

  # send packet
  def send(self, we, addr, be=0, wdata=0):                
    trace = "0001_"
    if self.verbose is True:
      if (we):
        print(f"SEND WRITE: addr=0x{addr:08X}, wdata=0x{wdata:08X}, byte_enable=0b{be:04b}")
      else:
        print(f"SEND READ : addr=0x{addr:08X}")

    # Begin with the 0 padding
    trace += self.get_bin_str(we, 1) + "_"
    trace += self.get_bin_str(be, self.byte_enable_width_p) + "_"
    trace += self.get_bin_str(addr, self.addr_width_p) + "_"
    trace += self.get_bin_str(wdata, self.data_width_p)

    self.fwrite.write(trace + "\n")
  
  # recv data
  def recv(self, cache_data):
    if self.verbose is True:
      print(f"RECV      : cache_data=0x{cache_data:08X}")

    trace = "0010_"
    trace += self.get_bin_str(0, self.packet_len-self.receive_data_len) + "_"
    trace += self.get_bin_str(cache_data, self.data_width_p)
  
    self.fwrite.write(trace + "\n")
    #print(trace)

  # done
  def done(self):
    trace = "0011_"
    trace += self.get_bin_str(0, self.packet_len)
    self.fwrite.write(trace + "\n")

  def finish(self):
    trace = "0100_"
    trace += self.get_bin_str(0, self.packet_len)
    self.fwrite.write(trace + "\n")

  # wait
  def wait(self, cycle):
    trace = "0110_"
    trace += self.get_bin_str(cycle, self.packet_len)
    self.fwrite.write(trace + "\n")
    
    trace = "0101_"
    trace += self.get_bin_str(0, self.packet_len)
    self.fwrite.write(trace + "\n")

  # nop
  def nop(self):
    trace = "0000_"
    trace += self.get_bin_str(0, self.packet_len)
    self.fwrite.write(trace + "\n")

  # get binary string (helper)
  def get_bin_str(self, val, width):
    return format(val, "0" + str(width) + "b")


