'''
Created on May 18, 2021

@author: mballance
'''
from vsc.model.constraint_inline_scope_model import ConstraintInlineScopeModel
from vsc.model.constraint_dist_model import ConstraintDistModel
from vsc.model.constraint_soft_model import ConstraintSoftModel

class ConstraintDistScopeModel(ConstraintInlineScopeModel):
    """Holds implementation data about dist constraint"""
    
    def __init__(self, dist_c, constraints=None):
        super().__init__(constraints)
        
        self.dist_c : ConstraintDistModel = dist_c
        
        self.dist_soft_c : ConstraintSoftModel = None
        
        # Indicates the current-target range. This is
        # updated during the weight-selection process
        self.target_range = 0
        
    def set_dist_soft_c(self, c : ConstraintSoftModel):
        self.addConstraint(c)
        self.dist_soft_c = c
        
    def accept(self, v):
        v.visit_constraint_dist_scope(self)