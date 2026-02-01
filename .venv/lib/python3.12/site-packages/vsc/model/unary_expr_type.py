'''
Created on Apr 28, 2020

@author: ballance
'''
from enum import Enum, auto

class UnaryExprType(Enum):
    Not = auto()
    
    @staticmethod
    def toString(op):
        return {
            UnaryExprType.Not : "!"
            }[op]