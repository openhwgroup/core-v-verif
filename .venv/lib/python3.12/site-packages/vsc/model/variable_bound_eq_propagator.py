'''
Created on May 31, 2020

@author: ballance
'''
from vsc.model.variable_bound_propagator import VariableBoundPropagator

class VariableBoundEqPropagator(VariableBoundPropagator):
    
    def __init__(self, target, eq_e, is_const):
        super().__init__(target)
        self.eq_e = eq_e
        self.is_const = is_const
        
    def propagate(self):
        should_propagate = False
        
        if self.is_const:
            # Domain of the target shrinks to be equal to eq_e
            eq_v = int(self.eq_e.val())
            range_l = self.target.domain.range_l
            if len(range_l) >= 1:
                if len(range_l) > 1 or not (range_l[0][0] == eq_v and range_l[0][1] == eq_v):
                    should_propagate = True
                    self.target.domain.range_l = [[eq_v, eq_v]]
                    
        return should_propagate
        