'''
Created on Aug 21, 2020

@author: ballance
'''
from vsc.model.model_visitor import ModelVisitor

from vsc.model.expr_dynamic_model import ExprDynamicModel


class DynamicExprResetVisitor(ModelVisitor):
    
    def __init__(self):
        pass
    
    def visit_expr_dynamic(self, e:ExprDynamicModel):
        e.reset()