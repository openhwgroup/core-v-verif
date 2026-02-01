'''
Created on Mar 13, 2020

@author: ballance
'''
from ucis.cover_type import CoverType

class MemCoverType(CoverType):
    
    def __init__(self):
        self.goal = 0
        self.limit = 0
        self.weight = 0
        super().__init__()

    def setCoverGoal(self, goal : int):
        self.goal = goal
    
    def getCoverGoal(self)->int:
        return self.goal
    
    def setCoverLimit(self, limit : int):
        self.limit = limit
    
    def getCoverLimit(self) -> int:
        return self.limit
    
    def setCoverWeight(self, weight : int):
        self.weight = weight
    
    def getCoverWeight(self) -> int:
        return self.weight
    