'''
Created on Apr 28, 2020

@author: ballance
'''
from vsc.model.expr_model import ExprModel
from vsc.model.unary_expr_type import UnaryExprType
from pyboolector import Boolector

class ExprUnaryModel(ExprModel):
    
    def __init__(self, op, e):
        super().__init__()
        self.expr = e
        self.op = op
        
    def build(self, btor : Boolector, ctx_width=-1):
        ret = None
        
        e_w = self.expr.width()
        if e_w > ctx_width:
            ctx_width = e_w
        
        
        if self.op == UnaryExprType.Not:
            ret = btor.Not(self.expr.build(btor, ctx_width))
        
        return ret
    
    def width(self):
        # Currently-supported unary expressions have the 
        # same width as the base expression
        return self.expr.width()
        
    def accept(self, v):
        v.visit_expr_unary(self)