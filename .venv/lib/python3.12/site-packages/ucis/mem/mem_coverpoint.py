'''
Created on Mar 22, 2020

@author: ballance
'''
from ucis import UCIS_COVERPOINT
from ucis.cover_index import CoverIndex
from ucis.coverpoint import Coverpoint
from ucis.mem.mem_cvg_scope import MemCvgScope
from ucis.source_info import SourceInfo


class MemCoverpoint(MemCvgScope,Coverpoint):
    
    def __init__(self,
                 parent,
                 name : str,
                 srcinfo : SourceInfo,
                 weight : int,
                 source):
        MemCvgScope.__init__(self, parent, name, srcinfo, weight, source, 
                             UCIS_COVERPOINT, 0)
        Coverpoint.__init__(self)
        
        