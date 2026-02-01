'''
Created on Jun 26, 2021

@author: mballance
'''
from vsc.model.value import Value
from vsc.model.value_scalar import ValueScalar

class ValueEnum(ValueScalar):
    
    def __init__(self, v):
        self.v = v