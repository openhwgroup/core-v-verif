'''
Created on Mar 21, 2020

@author: ballance
'''
from vsc.impl.vscobj_int import VscObjInt
from vsc.model.rand_state import RandState

class RandObjInt(VscObjInt):
    
    def __init__(self):
        super().__init__()
        self.randstate = None
        
    def get_randstate(self) -> RandState:
        if self.randstate is None:
            # Construct state
            self.randstate = RandState.mk()
            
        # Note: this is returned by reference. The
        # caller must clone as needed if saving 
        # a copy or mutating the state
        return self.randstate
    
    def set_randstate(self, rs):
        # Take a copy so we don't mutate source state
        self.randstate = rs.clone()

