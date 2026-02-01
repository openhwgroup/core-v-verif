'''
Created on Mar 12, 2020

@author: ballance
'''
from typing import List
from _ctypes import pointer, byref

from ucis import UCIS_VLOG, UCIS_COVERPOINT, UCIS_INT_SCOPE_GOAL, \
    UCIS_INT_CVG_ATLEAST, UCIS_STR_COMMENT, UCIS_INT_CVG_AUTOBINMAX, \
    UCIS_INT_CVG_PERINSTANCE, UCIS_INT_CVG_GETINSTCOV, \
    UCIS_INT_CVG_MERGEINSTANCES, UCIS_COVERINSTANCE
from ucis.cover_type import CoverType
from ucis.covergroup import Covergroup
from ucis.lib.lib_cvg_scope import LibCvgScope
from ucis.lib.lib_scope import LibScope
from ucis.lib.lib_source_info import _LibSourceInfo
from ucis.lib.libucis import get_lib
from ucis.source_info import SourceInfo
from ucis.source_t import SourceT
from ucis.lib.lib_cross import LibCross
from ctypes import c_void_p


class LibCovergroup(LibCvgScope, Covergroup):
    
    def __init__(self, db, obj):
        LibCvgScope.__init__(self, db, obj)
        Covergroup.__init__(self)

    def getPerInstance(self)->bool:
        return self.getIntProperty(-1, UCIS_INT_CVG_PERINSTANCE) == 1
    
    def setPerInstance(self, perinst):
        self.setIntProperty(-1, UCIS_INT_CVG_PERINSTANCE, 1 if perinst else 0)
    
    def getGetInstCoverage(self) -> bool:
        return self.getIntProperty(-1, UCIS_INT_CVG_GETINSTCOV) == 1
    
    def setGetInstCoverage(self, s : bool):
        self.setIntProperty(-1, UCIS_INT_CVG_GETINSTCOV, 1 if s else 0)
    
    def getMergeInstances(self)->bool:
        return self.getIntProperty(-1, UCIS_INT_CVG_MERGEINSTANCES) == 1
    
    def setMergeInstances(self, m:bool):
        self.setIntProperty(-1, UCIS_INT_CVG_MERGEINSTANCES, 1 if m else 0)

    def createCoverpoint(self, 
        name:str, 
        srcinfo:SourceInfo, 
        weight:int, 
        source)->CoverType:
        from ucis.lib.lib_coverpoint import LibCoverpoint

        cp_s = self.createScope(
            name, 
            srcinfo, 
            weight, 
            source, 
            UCIS_COVERPOINT, 
            0)
        
        return LibCoverpoint(self.db, cp_s.obj)
    
    def createCross(self, 
                    name : str, 
                    srcinfo : SourceInfo,
                    weight : int,
                    source : SourceT, 
                    points_l : List['Coverpoint']) -> CoverType:
        srcinfo_p = None if srcinfo is None else byref(_LibSourceInfo.ctor(srcinfo))

        points = (c_void_p * len(points_l))()
        for i,cp in enumerate(points_l):
            points[i] = cp.obj
            
        cr_o = get_lib().ucis_CreateCross(
            self.db,
            self.obj,
            str.encode(name),
            srcinfo_p,
            weight,
            source,
            len(points_l),
            byref(points))
        
        return LibCross(self.db, cr_o)
        raise NotImplementedError()
    
    def createCoverInstance(
            self,
            name:str,
            srcinfo:SourceInfo,
            weight:int,
            source)->'Covergroup':
        
        srcinfo_p = None if srcinfo is None else pointer(_LibSourceInfo.ctor(srcinfo))
        ci_obj = get_lib().ucis_CreateScope(
            self.db,
            self.obj,
            str.encode(name),
            srcinfo_p,
            weight,
            source,
            UCIS_COVERINSTANCE,
            0)
        
        
        return LibCovergroup(self.db, ci_obj)
