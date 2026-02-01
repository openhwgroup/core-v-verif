'''
Created on Jul 8, 2021

@author: mballance
'''
from vsc.model.expr_model import ExprModel
from vsc.visitors.expr2field_visitor import Expr2FieldVisitor
from vsc.model.field_composite_model import FieldCompositeModel


class ExprIndexedDynRefModel(ExprModel):
    """Constraint that is a reference to a dynamic-constraint block"""
    
    def __init__(self, root : ExprModel, idx):
        super().__init__()
        self.root = root
        self.idx = idx
        
    def build(self, btor, ctx_width=-1):
#        from vsc.visitors import ModelPrettyPrinter
        fm : FieldCompositeModel = Expr2FieldVisitor().field(self.root, True)
        c = fm.constraint_dynamic_model_l[self.idx]
        
        return c.build(btor)
        
    def accept(self, v):
        v.visit_expr_indexed_dynref(self)
        
    def width(self):
        return 1
    
    def is_signed(self):
        return False
    
    def __str__(self):
        return "ExprIndexedDynRefModel(" + self.c.name + ")"