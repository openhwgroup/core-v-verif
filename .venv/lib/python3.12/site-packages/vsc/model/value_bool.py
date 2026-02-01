'''
Created on May 16, 2020

@author: ballance
'''
from vsc.model.value import Value, ValueType

class ValueBool(Value):
    
    def __init__(self, v):
        super().__init__(ValueType.Bool)
        self.v = v
        
    def toString(self):
        return "True" if self.v else "False"
    
    @property
    def val(self):
        return self.v != 0
    
    def __bool__(self):
        return self.v
    
    def __int__(self):
        return 1 if self.v else 0
    
    def __eq__(self, rhs):
        return ValueBool(self.v == rhs.v)
    
    def __ne__(self, rhs):
        return ValueBool(self.v != rhs.v)
    