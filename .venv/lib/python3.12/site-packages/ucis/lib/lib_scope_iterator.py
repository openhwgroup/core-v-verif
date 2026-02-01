'''
Created on Mar 23, 2020

@author: ballance
'''
from ucis.scope_type_t import ScopeTypeT
from ucis.lib.libucis import get_lib

class LibScopeIterator(object):
    
    def __init__(self, db, scope, mask : ScopeTypeT):
        self.db = db
        self.iter = get_lib().ucis_ScopeIterate(db, scope, mask)
    
    def __iter__(self):
        return self
    
    def __next__(self):
        from .lib_scope import LibScope
        next = get_lib().ucis_ScopeScan(self.db, self.iter)
        
        if next is None:
            get_lib().ucis_FreeIterator(self.db, self.iter)
            raise StopIteration
        
        return LibScope(self.db, next)
        
        