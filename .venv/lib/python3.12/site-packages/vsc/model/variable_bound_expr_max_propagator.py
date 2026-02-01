'''
Created on Nov 7, 2020

@author: mballance
'''
from vsc.model.expr_model import ExprModel
from vsc.model.variable_bound_max_propagator import VariableBoundMaxPropagator


class VariableBoundExprMaxPropagator(VariableBoundMaxPropagator):
    
    def __init__(self,
                 target : 'VariableBoundModel',
                 max_e : ExprModel):
        super().__init__(target)
        self.max_e = max_e

    def max(self):
        return int(self.max_e.val())
    
    