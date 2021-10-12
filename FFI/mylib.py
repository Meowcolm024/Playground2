import ctypes
import sys
import os 

dir_path = os.path.dirname(os.path.realpath(__file__))
handle = ctypes.CDLL(dir_path + "/libTest.so")     

handle.hello.argtypes = [ctypes.c_int] 
  
def hello(num):
    handle.hello(num)
