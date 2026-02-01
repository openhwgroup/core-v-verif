'''
Created on May 23, 2021

@author: mballance
'''
from vsc.model.constraint_soft_model import ConstraintSoftModel
from vsc.model.model_visitor import ModelVisitor


class ClearSoftPriorityVisitor(ModelVisitor):
    
    def __init__(self):
        super().__init__()
        
    def clear(self, e):
        e.accept(self)
        
    def visit_constraint_soft(self, c:ConstraintSoftModel):
        c.priority = 0
        