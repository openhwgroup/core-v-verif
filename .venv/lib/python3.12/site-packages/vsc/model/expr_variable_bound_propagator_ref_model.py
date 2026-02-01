'''
Created on May 30, 2020

@author: ballance
'''
from vsc.model.expr_model import ExprModel
from vsc.model.variable_bound_propagator import VariableBoundPropagator

class ExprVariableBoundPropagatorRefModel(ExprModel):
    
    def __init__(self,
                 ref : VariableBoundPropagator,
                 ref_max : bool):
        super().__init__()
        self.ref = ref
        self.ref_max = ref_max
        
    def val(self):
        # TODO: return min or max value of the propagator
        ExprModel.val(self)
        
    def build(self, btor):
        raise Exception("")
        ExprModel.build(self, btor)
        
        