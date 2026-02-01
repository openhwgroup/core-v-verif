'''
Created on Jan 12, 2020

@author: ballance
'''
from ucis.cover_item import CoverItem

class MemCoverItem(CoverItem):
    
    def __init__(self, parent, name, data, sourceinfo):
        super().__init__()
        self.m_stmt_idx = 0
        self.m_parent = parent
        self.m_name = name
        self.m_data = data # TODO: copy
        self.m_sourceinfo = sourceinfo # TODO: copy

    def getStmtIndex(self)->int:
        return self.m_stmt_idx

    def setStmtIndex(self, i):
        self.m_stmt_idx = i
        
    