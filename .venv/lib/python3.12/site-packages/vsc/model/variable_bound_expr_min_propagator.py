'''
Created on Nov 7, 2020

@author: mballance
'''
from vsc.model.expr_model import ExprModel
from vsc.model.variable_bound_min_propagator import VariableBoundMinPropagator


class VariableBoundExprMinPropagator(VariableBoundMinPropagator):
    
    def __init__(self,
                 target : 'VariableBoundModel',
                 min_e : ExprModel):
        super().__init__(target)
        self.min_e = min_e

    def min(self):
        return int(self.min_e.val())
    