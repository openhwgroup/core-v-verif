'''
Created on Nov 7, 2020

@author: mballance
'''
from vsc.model.variable_bound_bounds_max_propagator import VariableBoundBoundsMaxPropagator
from vsc.model.variable_bound_bounds_min_propagator import VariableBoundBoundsMinPropagator
from vsc.model.variable_bound_propagator import VariableBoundPropagator


class VariableBoundVarEqPropagator(VariableBoundPropagator):
    
    def __init__(self, target, other):
        super().__init__(target)
        self.max_p1 = VariableBoundBoundsMaxPropagator(target, other)
        self.max_p2 = VariableBoundBoundsMaxPropagator(other, target)
        self.min_p1 = VariableBoundBoundsMinPropagator(target, other)
        self.min_p2 = VariableBoundBoundsMinPropagator(other, target)
        
    def propagate(self):
        ret = False
        ret |= self.max_p1.propagate()
        ret |= self.max_p2.propagate()
        ret |= self.min_p1.propagate()
        ret |= self.min_p2.propagate()
        
        return ret
        