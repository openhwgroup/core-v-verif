'''
Created on May 16, 2020

@author: ballance
'''
from enum import Enum, auto

class ValueType(Enum):
    Scalar = auto()
    Bool = auto()
    Enum = auto()
    String = auto()

class Value(object):
    
    def __init__(self, t : ValueType):
        self.t = t
        pass
    
    def toString(self):
        raise Exception("toString not implemented for class " + str(type(self)))

    @property
    def val(self):
        raise Exception("val not implemented for class " + str(type(self)))
    
    def __int__(self):
        raise Exception("__int__ not implemented for class " + str(type(self)))

    def __eq__(self, rhs):
        raise Exception("__eq__ not implemented for class " + str(type(self)))
    
    def __ne__(self, rhs):
        raise Exception("__ne__ not implemented for class " + str(type(self)))
    
    def __gt__(self, rhs):
        raise Exception("__gt__ not implemented for class " + str(type(self)))
    
    def __ge__(self, rhs):
        raise Exception("__ge__ not implemented for class " + str(type(self)))
    
    def __lt__(self, rhs):
        raise Exception("__gt__ not implemented for class " + str(type(self)))
    
    def __le__(self, rhs):
        raise Exception("__ge__ not implemented for class " + str(type(self)))
    
    def __add__(self, rhs):
        raise Exception("__add__ not implemented for class " + str(type(self)))
    
    def __sub__(self, rhs):
        raise Exception("__add__ not implemented for class " + str(type(self)))