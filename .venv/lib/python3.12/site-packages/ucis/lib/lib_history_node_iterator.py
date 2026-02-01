'''
Created on Mar 22, 2020

@author: ballance
'''
from ucis.lib.libucis import get_lib
from ucis.lib.lib_history_node import LibHistoryNode


class LibHistoryNodeIterator(object):
    
    def __init__(self, db, hist_obj, kind):
        self.db = db
        self.iter = get_lib().ucis_HistoryIterate(self.db, hist_obj, kind)
        
    def __iter__(self):
        return self
    
    def __next__(self):
        next = get_lib().ucis_HistoryScan(self.db, self.iter)
        
        if next is None:
            get_lib().ucis_FreeIterator(self.iter)
            raise StopIteration
        
        return LibHistoryNode(self.db, next)
        
        
        
        