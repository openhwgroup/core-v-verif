'''
Created on Jan 12, 2020

@author: ballance
'''
from ucis.mem.mem_scope import MemScope
from ucis.cvg_scope import CvgScope

class MemCvgScope(MemScope,CvgScope):
    
    def __init__(self,
                 parent,
                 name,
                 srcinfo,
                 weight,
                 source,
                 type,
                 flags):
        MemScope.__init__(self, parent, name, srcinfo, weight, source, type, flags)
        CvgScope.__init__(self)
        self.m_at_least = 1
        self.m_auto_bin_max = 64
        self.m_detect_overlap = True
        self.m_strobe = 0
        self.m_comment = ""
        
    def getAtLeast(self)->int:
        return self.m_at_least
    
    def setAtLeast(self, atleast):
        self.m_at_least = atleast
    
    def getAutoBinMax(self)->int:
        return self.m_auto_bin_max
    
    def setAutoBinMax(self, auto_max):
        self.m_auto_bin_max = auto_max
    
    def getDetectOverlap(self)->bool:
        return self.m_detect_overlap
    
    def setDetectOverlap(self, detect:bool):
        self.m_detect_overlap = detect
    
    def getStrobe(self)->int:
        return self.m_strobe
    
    def setStrobe(self, s):
        self.m_strobe = s
        
    def setGetInstCoverage(self, en:bool):
        self.m_get_inst_coverage = en
        
    def getComment(self)->str:
        return self.m_comment
    
    def setComment(self, c:str):
        self.m_comment = c
        
