import ctypes
import sys
import os 

dir_path = os.path.dirname(os.path.realpath(__file__))
handle = ctypes.CDLL(dir_path + "/libTest.so")     

handle.MyFunction.argtypes = [ctypes.c_int] 
  
def MyFunction(num):
    return handle.MyFunction(num) 
