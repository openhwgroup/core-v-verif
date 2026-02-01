'''
Created on May 19, 2020

@author: ballance
'''
from vsc.model.model_visitor import ModelVisitor
from vsc.model.constraint_override_model import ConstraintOverrideModel
from vsc.visitors.constraint_override_visitor import ConstraintOverrideVisitor

class ConstraintOverrideRollbackVisitor(ConstraintOverrideVisitor):
    """Removes all, or certain levels, of rollback constrains"""
    
    def __init__(self, rollback=-1):
        super().__init__()
        self.rollback = rollback
        
    @staticmethod
    def rollback(m):
        v = ConstraintOverrideRollbackVisitor()
        m.accept(v)
        
    def visit_constraint_override(self, c : ConstraintOverrideModel):
        c.depth -= 1
        if c.depth <= 0:
            # roll this constraint back to the original
            self.scope_s[-1].constraint_l[self.scope_i] = c.orig_constraint
    
    