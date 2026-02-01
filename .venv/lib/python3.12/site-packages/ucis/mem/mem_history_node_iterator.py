'''
Created on Mar 22, 2020

@author: ballance
'''
from typing import List
from ucis.history_node import HistoryNode
from ucis.mem.mem_history_node import MemHistoryNode
from ucis.history_node_kind import HistoryNodeKind

class MemHistoryNodeIterator(object):
    
    def __init__(self, history_nodes : List[MemHistoryNode], kind : HistoryNodeKind):
        self.idx = 0
        self.history_nodes = history_nodes
        self.kind = kind
        
    def __iter__(self):
        return self
    
    def __next__(self):
        next = None
        
        while self.idx < len(self.history_nodes):
            hn = self.history_nodes[self.idx]
            if self.kind == HistoryNodeKind.ALL or hn.getKind() == self.kind:
                next = hn
            self.idx += 1
            if next is not None:
                break
            
        if next is None:
            raise StopIteration
        
        return next
                
        