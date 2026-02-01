'''
Created on May 30, 2020

@author: ballance
'''
from vsc.model.variable_bound_propagator import VariableBoundPropagator

class VariableBoundMaxPropagator(VariableBoundPropagator):
    
    def __init__(self,
                 target : 'VariableBoundModel'):
        super().__init__(target)
        
    def max(self):
        raise NotImplementedError("max")
        
    def propagate(self):
        # Obtain the max value from the
        max_v = self.max()
  
        range_l = self.target.domain.range_l
        i=len(range_l)-1
        
#        print("Max: range_l=" + str(range_l) + " max_v=" + str(max_v))

        # Note: assume domain ranges are ordered
        # Find the first interval where the minimum is less than the max
        while i > 0:
            if range_l[i][0] <= max_v:
                break
            else:
                i -= 1
            
        must_propagate = False
        if i >= 0:
#            print("i: " + str(i) + " " + str(self.target.domain.range_l[i][0]))
            if range_l[i][1] > max_v:
                range_l[i][1] = max_v
                must_propagate = True
                
            if i < len(range_l)-1:
                # Need to trim off full range elements
                must_propagate = True
#                print("Removing domain element " + str(range_l[i+1]))
                self.target.domain.range_l = range_l[:i+1]
        else:
#            print("ran off the end")
            pass
            
        return must_propagate
