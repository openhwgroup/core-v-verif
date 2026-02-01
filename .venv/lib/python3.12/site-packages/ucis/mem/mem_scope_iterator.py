'''
Created on Mar 22, 2020

@author: ballance
'''
from typing import List


class MemScopeIterator(object):
    
    def __init__(self, nodes : List['MemScope'], mask):
        self.nodes = nodes
        self.idx = 0
        self.mask = mask
        
    def __iter__(self):
        return self
    
    def __next__(self):
        next = None

        while next is None and self.idx < len(self.nodes):
            n = self.nodes[self.idx]
            # TODO: qualify mask
            if (n.getScopeType() & self.mask) != 0:
                next = n

            self.idx += 1
            
            if next is not None:
                break

        if next is None:        
            raise StopIteration
        return next