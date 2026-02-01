'''
Created on Mar 13, 2020

@author: ballance
'''
from ucis.lib.lib_obj import LibObj
from ucis.cover_index import CoverIndex
from ucis.lib import libucis

class LibCoverIndex(LibObj, CoverIndex):
    
    def __init__(
            self, 
            db, 
            obj, # The object to which this index is relative 
            index):
        super().__init__(db, obj)
        self.index = index