'''
Created on Jan 12, 2020

@author: ballance
'''
from enum import IntEnum, auto

class ToggleDirT(IntEnum):
    
    INTERNAL = 1   # non-port: internal wire or variable
    IN = auto()    # input port
    OUT = auto()   # output port
    INOUT = auto() # inout port
