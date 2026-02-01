'''
Created on May 19, 2020

@author: ballance
'''
from typing import List

from vsc.model.constraint_inline_scope_model import ConstraintInlineScopeModel
from vsc.model.constraint_override_model import ConstraintOverrideModel
from vsc.model.constraint_scope_model import ConstraintScopeModel
from vsc.visitors.constraint_copy_builder import ConstraintCopyBuilder


class ConstraintOverrideVisitor(ConstraintCopyBuilder):
    
    def __init__(self):
        super().__init__()
        self.scope_s : List[ConstraintScopeModel] = []
        self.scope_i = 0
        
    def visit_constraint_scope(self, c:ConstraintScopeModel):
        self.scope_s.append(c)
        for i,cc in enumerate(c.constraint_l):
            self.scope_i = i
            cc.accept(self)
        self.scope_s.pop()
            
    def visit_constraint_inline_scope(self, c:ConstraintInlineScopeModel):
        self.scope_s.append(c)
        for i,cc in enumerate(c.constraint_l):
            self.scope_i = i
            cc.accept(self)
        self.scope_s.pop()
            
    def override_constraint(self, new_constraint):
        """Replace the active constraint with a replacement"""
        self.scope_s[-1].constraint_l[self.scope_i] = ConstraintOverrideModel(
            self.scope_s[-1].constraint_l[self.scope_i],
            new_constraint)
        

        