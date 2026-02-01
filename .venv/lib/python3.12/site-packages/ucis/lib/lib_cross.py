'''
Created on Feb 1, 2021

@author: mballance
'''
from ucis import UCIS_CVGBIN, UCIS_IS_32BIT, UCIS_HAS_GOAL, UCIS_HAS_WEIGHT
from ucis.cover_data import CoverData
from ucis.cover_index import CoverIndex
from ucis.cross import Cross
from ucis.lib.lib_cvg_scope import LibCvgScope
from ucis.source_info import SourceInfo


class LibCross(LibCvgScope, Cross):
    
    def __init__(self, db, obj):
        LibCvgScope.__init__(self, db, obj)
        Cross.__init__(self)

    def createBin(
        self,
        name:str, 
        srcinfo:SourceInfo, 
        at_least:int, 
        count:int,
        binrhs) -> CoverIndex:
        coverdata = CoverData(
            UCIS_CVGBIN,
            (UCIS_IS_32BIT|UCIS_HAS_GOAL|UCIS_HAS_WEIGHT))
        coverdata.data = count
        coverdata.at_least = at_least
        coverdata.goal = 1
        # TODO: bring weight in via API?
        coverdata.weight = 1
        
        index = self.createNextCover(
            name, 
            coverdata,
            srcinfo)
        
        return index