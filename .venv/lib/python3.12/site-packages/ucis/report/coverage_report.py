'''
Created on Mar 27, 2020

@author: ballance
'''
from ucis.covergroup import Covergroup
from ucis.cover_item import CoverItem
from typing import List, Dict

class CoverageReport(object):
    """
    Root coverage-report object
    """
    
    def __init__(self):
        #: List of (type) covergroups
        self.covergroups = []
        
        #: Map of (type) covergroup name to object
        self.covergroup_m = {}
        
        #: Coverage percentage achieved by all covergroups
        self.coverage = 0.0
    
    def add_covergroup(self,cg)->Covergroup:
        self.covergroups.append(cg)
        return cg
    
    class CoverItem(object):
        """
        Base type for covergroups and coverpoints
        """
        
        def __init__(self, name):
            
            #: Name of the cover item
            self.name = name
            
            #: Coverage percentage achieved by the cover item
            self.coverage = 0.0
            
            #: Weight given to this item when calculating coverage %
            self.weight = 1
            
    class Covergroup(CoverItem):
        """
        Contains coverage data for a covergroup type or instance
        """
        
        def __init__(self, name, instname):
            super().__init__(name)
            
            #: Covergroup instance name
            self.instname = instname

            #: List of coverpoints in the covergroup           
            self.coverpoints : List[CoverageReport.Coverpoint] = []
            
            #: Map of coverpoint name to object
            self.coverpoint_m : Dict[str,CoverageReport.Coverpoint] = {}
            
            #: List of cross points in the covergroup
            self.crosses : List[CoverageReport.Cross] = []
            
            #: Map of cross name to object
            self.cross_m : Dict[str,CoverageReport.Cross] = {}
            
            #: List of covergroup sub-instances. This is only
            #: populated when `self` is a type covergroup
            self.covergroups : List[CoverageReport.Covergroup] = []

            #: Map of covergroup instance names to object
            #: This is only populated when `self` is a type covergroup
            self.covergroup_m : Dict[str,CoverageReport.Covergroup] = {}
            
        def add_coverpoint(self, cp)->'Coverpoint':
            self.coverpoints.append(cp)
            self.coverpoint_m[cp.name] = cp
            return cp
            

    class Coverpoint(CoverItem):
        """
        Contains coverage data about a coverpoint 
        """

        def __init__(self, name):
            super().__init__(name)
            self.bins : List[CoverageReport.CoverBin] = []
            self.ignore_bins : List[CoverageReport.CoverBin] = []
            self.illegal_bins = []
            
    class Cross(CoverItem):
        """
        Contains coverage data for a cross
        """
        
        def __init__(self, name):
            super().__init__(name)
            self.bins = []
            
    class CoverBin(object):
        
        def __init__(self, name, goal, count):
            self.name = name
            self.goal = goal
            self.count = count

        @property            
        def hit(self):
            return self.count >= self.goal
        

