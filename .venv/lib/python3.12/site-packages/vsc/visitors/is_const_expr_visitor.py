'''
Created on May 30, 2020

@author: ballance
'''
from vsc.model.model_visitor import ModelVisitor

class IsConstExprVisitor(ModelVisitor):
    
    def __init__(self):
        super().__init__()
        self._is_const = False
        
    def is_const(self, e) -> bool:
        self._is_const = True
        e.accept(self)
        return self._is_const

    def visit_expr_fieldref(self, e):
        self._is_const = False
        