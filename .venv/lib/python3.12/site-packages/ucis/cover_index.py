'''
Created on Mar 13, 2020

@author: ballance
'''
from ucis.cover_data import CoverData
from ucis.source_info import SourceInfo

class CoverIndex(object):
    
    def __init__(self):
        super().__init__()
        
    def getName(self)->str:
        raise NotImplementedError()
    
    def getCoverData(self)->CoverData:
        raise NotImplementedError()
    
    def getSourceInfo(self)->SourceInfo:
        raise NotImplementedError()
    
    def incrementCover(self, amt=1):
        raise NotImplementedError()
        
        
    