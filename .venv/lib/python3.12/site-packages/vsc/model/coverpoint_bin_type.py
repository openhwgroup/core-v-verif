'''
Created on Oct 18, 2021

@author: mballance
'''
from enum import Enum, auto


class CoverpointBinType(Enum):
    Bins    = auto()
    Ignore  = auto()
    Illegal = auto()
