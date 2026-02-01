'''
Created on Aug 9, 2020

@author: ballance
'''
from typing import List

from vsc.model.constraint_model import ConstraintModel
from vsc.model.dist_weight_expr_model import DistWeightExprModel
from vsc.model.expr_fieldref_model import ExprFieldRefModel


class ConstraintDistModel(ConstraintModel):
    
    def __init__(self,
                 lhs : ExprFieldRefModel,
                 weights : List[DistWeightExprModel]):
        self.lhs = lhs
        self.weights = weights
        
        pass
    
    def accept(self, v):
        v.visit_constraint_dist(self)
        