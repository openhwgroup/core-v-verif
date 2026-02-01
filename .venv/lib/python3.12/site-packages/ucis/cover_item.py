'''
Created on Jan 12, 2020

@author: ballance
'''
from ucis.obj import Obj
from ucis.unimpl_error import UnimplError

class CoverItem(Obj):
    
    def __init__(self):
        super().__init__()
        
    def getStmtIndex(self)->int:
        raise UnimplError()
    
    def setStmtIndex(self, i):
        raise UnimplError()
        