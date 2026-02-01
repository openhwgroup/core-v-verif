'''
Created on Nov 5, 2020

@author: mballance
'''
from vsc.model.model_visitor import ModelVisitor

class IsNonRandExprVisitor(ModelVisitor):
    
    def __init__(self):
        super().__init__()
        self._is_nonrand = True
        
        
    def is_nonrand(self, e) -> bool:
        self._is_nonrand = True
        e.accept(self)
        return self._is_nonrand

    def visit_expr_fieldref(self, e):
        self._is_nonrand = not e.fm.is_used_rand
        
        