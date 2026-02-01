'''
Created on Jan 12, 2020

@author: ballance
'''
from ucis.du_scope import DUScope
from ucis.flags_t import FlagsT
from ucis.mem.mem_scope import MemScope
from ucis.scope_type_t import ScopeTypeT
from ucis.source_info import SourceInfo
from ucis.source_t import SourceT
from ucis.unimpl_error import UnimplError


class MemDUScope(MemScope, DUScope):
    
    def __init__(self,
                 parent : 'MemScope',
                 name : str,
                 srcinfo : SourceInfo,
                 weight : int,
                 source : SourceT,
                 type :ScopeTypeT,
                 flags : FlagsT):
        super().__init__(parent, name, srcinfo, weight, source, type, flags)
        self.m_du_signature = None
        
    def getSignature(self):
        return self.m_du_signature
    
    def setSignature(self, sig):
        self.m_du_signature = sig
        
    def createScope(self,
                name : str,
                srcinfo : SourceInfo,
                weight : int,
                source : SourceT,
                type : ScopeTypeT,
                flags : FlagsT):
        # Creates a type scope and associates source information with it
        if ScopeTypeT.DU_ANY(type):
            ret = MemDUScope(self, name, srcinfo, weight,
                              source, type, flags)
            self.add_child(ret)
        else:
            raise UnimplError()