'''
Created on Jan 12, 2020

@author: ballance
'''
from ucis.mem.mem_instance_scope import MemInstanceScope
from ucis.source_t import SourceT
from ucis.scope_type_t import ScopeTypeT

class MemToggleInstanceScope(MemInstanceScope):
    
    def __init__(self,
                parent,
                name,
                canonical_name,
                flags,
                toggle_metric,
                toggle_type,
                toggle_dir):
        super().__init__(parent, name, None, 0, SourceT.NONE, ScopeTypeT.TOGGLE, None, flags)