'''
Created on Sep 10, 2020

@author: ballance
'''
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.model_visitor import ModelVisitor


class RefFieldsPostRandVisitor(ModelVisitor):
    
    def __init__(self):
        super().__init__()
        
    def visit_expr_fieldref(self, e):
        # Capture solving values and mark fields not-used-rand
        e.fm.post_randomize()
        e.fm.set_used_rand(False)
        