'''
Created on Mar 24, 2020

@author: ballance
'''
from ucis.mem.mem_coverpoint import MemCoverpoint
from ucis.cross import Cross
from ucis.source_t import SourceT
from ucis.source_info import SourceInfo
from typing import List
from ucis import UCIS_CROSS

class MemCross(MemCoverpoint,Cross):
    
    def __init__(self,
                 parent,
                 name : str,
                 srcinfo : SourceInfo,
                 weight : int,
                 source : SourceT,
                 coverpoints : List['MemCoverpoint']
                 ):
        MemCoverpoint.__init__(self, parent, name, srcinfo, weight, source)
        self.m_type = UCIS_CROSS
        Cross.__init__(self)
        
        self.coverpoints = coverpoints
        
    def getNumCrossedCoverpoints(self)->int:
        return len(self.coverpoints)
    
    def getIthCrossedCoverpoint(self, index)->'Coverpoint':
        return self.coverpoints[index]
    
    