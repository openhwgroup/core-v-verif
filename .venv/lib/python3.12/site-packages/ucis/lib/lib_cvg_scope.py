'''
Created on Mar 14, 2020

@author: ballance
'''
from ucis import UCIS_INT_CVG_ATLEAST, UCIS_INT_CVG_AUTOBINMAX,\
    UCIS_INT_CVG_DETECTOVERLAP, UCIS_INT_CVG_STROBE, UCIS_STR_COMMENT
from ucis.cvg_scope import CvgScope
from ucis.lib.lib_obj import LibObj
from ucis.lib.lib_scope import LibScope


class LibCvgScope(LibScope, CvgScope):
    
    def __init__(self, db, obj):
        LibScope.__init__(self, db, obj)
        CvgScope.__init__(self)
        
    def getAtLeast(self)->int:
        return self.getIntProperty(-1, UCIS_INT_CVG_ATLEAST)
    
    def setAtLeast(self, atleast):
        self.setIntProperty(-1, UCIS_INT_CVG_ATLEAST, atleast)
        
    def getAutoBinMax(self)->int:
        return self.getIntProperty(-1, UCIS_INT_CVG_AUTOBINMAX)
    
    def setAutoBinMax(self, auto_max):
        self.setIntProperty(-1, UCIS_INT_CVG_AUTOBINMAX, auto_max)
        
    def getDetectOverlap(self)->bool:
        return self.getIntProperty(-1, UCIS_INT_CVG_DETECTOVERLAP) == 1
    
    def setDetectOverlap(self, detect:bool):
        self.setIntProperty(-1, UCIS_INT_CVG_DETECTOVERLAP, 
                        1 if detect else 0)
        
    def getStrobe(self)->bool:
        return self.getIntProperty(-1, UCIS_INT_CVG_STROBE) == 1
    
    def setStrobe(self, s : bool):
        self.setIntProperty(-1, UCIS_INT_CVG_STROBE,
                            1 if s else 0)
        
    def getComment(self)->str:
        return self.getStringProperty(-1, UCIS_STR_COMMENT)
    
    def setComment(self, c:str):
        return self.setStringProperty(-1, UCIS_STR_COMMENT, c)
                