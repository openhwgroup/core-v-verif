'''
Created on Mar 23, 2020

@author: ballance
'''
from ucis.cover_index import CoverIndex
from ucis.cover_data import CoverData
from ucis.source_info import SourceInfo

class MemCoverIndex(CoverIndex):
    
    def __init__(self, 
                 name : str,
                 data : CoverData,
                 srcinfo : SourceInfo):
        CoverIndex.__init__(self)
        self.name = name
        self.data = data
        self.srcinfo = srcinfo
        
    def getName(self)->str:
        return self.name
        
    def getCoverData(self)->CoverData:
        return self.data
    
    def getSourceInfo(self)->SourceInfo:
        return self.srcinfo
    
    def incrementCover(self, amt=1):
        self.data.data += amt
        
        