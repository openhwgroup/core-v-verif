

# Created on Apr 7, 2020
#
# @author: ballance


class CoverageOptionsModel(object):
    
    def __init__(self):
        self.weight = 1
        self.goal = 100
        self.comment = ""
        self.at_least = 1
        self.auto_bin_max = 64
        
    def clone(self):
        ret = CoverageOptionsModel()
        ret.weight = self.weight
        ret.goal = self.goal
        ret.comment = self.comment
        ret.at_least = self.at_least
        ret.auto_bin_max = self.auto_bin_max
        
        return ret
