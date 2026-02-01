'''
Created on Jun 13, 2020

@author: ballance
'''
from vsc.model.constraint_scope_model import ConstraintScopeModel

class ConstraintInlineScopeModel(ConstraintScopeModel):
    """Constraint scope that is the result of an expansion"""
    
    def __init__(self, constraints=None):
        super().__init__(constraints)
        
    def accept(self, v):
        v.visit_constraint_inline_scope(self)
        
    def clone(self, deep=False)->'ConstraintModel':
        if deep:
            ret = ConstraintInlineScopeModel()
            for c in self.constraint_l:
                ret.constraint_l.append(c.clone(deep))
        else:
            ret = ConstraintInlineScopeModel(self.constraint_l)
                
        return ret
    