'''
Created on Jan 12, 2020

@author: ballance
'''
from ucis.scope import Scope
from ucis.unimpl_error import UnimplError
from ucis.str_property import StrProperty


class DUScope(Scope):
    
    def __init__(self):
        super().__init__()
        
    def getSignature(self):
        raise UnimplError()
    
    def setSignature(self, sig):
        raise UnimplError()
    
    def getStringProperty(
            self,
            coverindex : int,
            property : StrProperty) -> str:
        if property == StrProperty.DU_SIGNATURE:
            return self.getSignature()
        else:
            return super().getStringProperty(coverindex, property)
    
    def setStringProperty(
            self,
            coverindex : int,
            property : StrProperty,
            value : str):
        if property == StrProperty.DU_SIGNATURE:
            self.setSignature(value)
        else:
            self.setStringProperty(coverindex, property, value)
        
    def accept(self, v):
        v.visit_du_scope(self)
        