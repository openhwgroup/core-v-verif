'''
Created on Mar 12, 2020

@author: ballance
'''
from ucis import UCIS_CVGBIN, UCIS_IS_32BIT, UCIS_HAS_GOAL, UCIS_HAS_WEIGHT
from ucis.cover_data import CoverData
from ucis.coverpoint import Coverpoint
from ucis.lib.lib_scope import LibScope
from ucis.source_info import SourceInfo

from ucis.cover_index import CoverIndex
from ucis.lib.lib_cvg_scope import LibCvgScope


class LibCoverpoint(LibCvgScope, Coverpoint):
    
    def __init__(self, db, obj):
        LibCvgScope.__init__(self, db, obj)
        Coverpoint.__init__(self)
        
    def createBin(
        self, 
        name:str, 
        srcinfo:SourceInfo, 
        at_least:int, 
        count:int,
        binrhs,
        kind=UCIS_CVGBIN) -> CoverIndex:
        coverdata = CoverData(
            kind,
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
        