'''
Created on May 30, 2020

@author: ballance
'''
from vsc.model.variable_bound_propagator import VariableBoundPropagator

class VariableBoundMinPropagator(VariableBoundPropagator):
    
    def __init__(self,
                 target : 'VariableBoundModel'):
        super().__init__(target)

    def min(self):
        raise NotImplementedError("min")
            
    def propagate(self):
        # Obtain the max value from the
        min_v = self.min()
        
        range_l = self.target.domain.range_l
        
#        print("Min: range_l=" + str(range_l) + " min_v=" + str(min_v))

        # Note: assume domain ranges are ordered
        # Find the first interval where the min_v is greater than 
        # the minimum of the interval
        i=len(range_l)-1
        while i >=0 and min_v <= range_l[i][0]:
            i -= 1
            
#        print("  i=" + str(i))

        must_propagate = False
        if i < len(range_l):
            if i > 0:
                # Need to trim off full range elements
                must_propagate = True
                self.target.domain.range_l = range_l[i:]

            if min_v > range_l[0][0]:
                range_l[0][0] = min_v
                must_propagate = True
        else:
#            print("ran off the end")
            pass
            
        return must_propagate
