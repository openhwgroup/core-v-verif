'''
Created on Aug 9, 2020

@author: ballance
'''
from vsc.model.expr_model import ExprModel

class DistWeightExprModel(ExprModel):
    
    def __init__(self,
                 rng_lhs : ExprModel,
                 rng_rhs : ExprModel,
                 weight : ExprModel):
        self.rng_lhs = rng_lhs
        self.rng_rhs = rng_rhs
        self.weight = weight
    
    def accept(self, v):
        v.visit_dist_weight(self)
