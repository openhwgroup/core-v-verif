'''
Created on Mar 23, 2020

@author: ballance
'''
from typing import List
from ucis.mem.mem_cover_index import MemCoverIndex
from ucis.cover_type_t import CoverTypeT

class MemCoverIndexIterator(object):
    
    def __init__(self, coveritems : List[MemCoverIndex], mask : CoverTypeT):
        self.coveritems = coveritems
        self.mask = mask
        self.idx = 0
        
    def __iter__(self):
        return self
    
    def __next__(self):
        next = None
        
        while self.idx < len(self.coveritems) and next is None:
            n = self.coveritems[self.idx]

            if (n.data.type & self.mask) != 0:
                next = n
            self.idx += 1

        if next is None:
            raise StopIteration
        
        return next