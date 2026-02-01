'''
Created on May 19, 2020

@author: ballance
'''
from vsc.model.constraint_model import ConstraintModel


class ConstraintOverrideModel(ConstraintModel):
    """Enables replacing one constraint with another"""
    
    def __init__(self, orig_constraint, new_constraint):
        super().__init__()
        self.new_constraint = new_constraint
        self.orig_constraint = orig_constraint
        self.depth = 1
        
    def build(self, btor):
        return self.new_constraint.build(btor)
        
    def accept(self, v):
        v.visit_constraint_override(self)
        
        