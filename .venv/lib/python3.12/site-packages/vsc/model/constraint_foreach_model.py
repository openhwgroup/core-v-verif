'''
Created on May 17, 2020

@author: ballance
'''
from typing import List

from vsc.model.constraint_scope_model import ConstraintScopeModel
from vsc.model.field_scalar_model import FieldScalarModel


class ConstraintForeachModel(ConstraintScopeModel):
    
    def __init__(self, lhs : 'FieldArrayModel'):
        super().__init__()
        self.lhs = lhs
        self.index = FieldScalarModel(
            "index", 
            32, 
            False, 
            False)

        self.iterator = FieldScalarModel(
            "iterator", 
            32, 
            False, 
            False)
        
        
    def build(self, btor)->'BoolectorNode':
        # Unroll the constraints
        size = int(self.lhs.size.get_val())
        ret_l = []
        
        for i in range(size):
            # Set the index variable
            self.index.set_val(i)
            
            # Build out the constraints for this index
            # Note: some could be redundant
            for c in self.constraint_l:
                ret_l.append(c.build(btor))
                
        return btor.And(*ret_l)
    
    def accept(self, v):
        v.visit_constraint_foreach(self)
    
    def clone(self, deep=False)->'ConstraintModel':
        ret = ConstraintForeachModel(self.lhs)
        
        if deep:
            for c in self.constraint_l:
                ret.constraint_l.append(c.clone(deep))
                
        return ret
