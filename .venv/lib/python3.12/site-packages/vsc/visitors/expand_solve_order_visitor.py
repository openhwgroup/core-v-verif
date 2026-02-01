'''
Created on May 25, 2021

@author: mballance
'''
from vsc.model.field_array_model import FieldArrayModel
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.model_visitor import ModelVisitor


class ExpandSolveOrderVisitor(ModelVisitor):
    
    def __init__(self, order_m=None, lhs=True):
        super().__init__()
        if order_m is None:
            self.order_m = {}
        else:
            self.order_m = order_m
        self.lhs = lhs
            
    def expand(self, a, b):
        self.a = a
        self.b = b
        
        if self.lhs:
            a.accept(self)
        else:
            b.accept(self)

    def visit_scalar_field(self, f:FieldScalarModel):
        if self.lhs:
            # Now, visit rhs
            ExpandSolveOrderVisitor(self.order_m, lhs=False).expand(f, self.b)
        else:
            if not self.a in self.order_m.keys():
                self.order_m[self.a] = set()
            self.order_m[self.a].add(f)
        
