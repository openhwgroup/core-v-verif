

# Created on Mar 6, 2020
#
# @author: ballance

from vsc.model.expr_model import ExprModel
from builtins import callable

class ExprRefModel(ExprModel):
    
    def __init__(self, 
            ref : callable,
            ref_width,
            ref_signed):
        super().__init__()
        self.ref = ref
        self.ref_width = ref_width
        self.ref_signed = ref_signed
        
    def build(self, btor, ctx_width=-1):
        return btor.Const(self.val(), self.ref_width())
        
    def is_signed(self):
        return self.ref_signed
    
    def width(self):
        return self.ref_width
        
    def accept(self, v):
        v.visit_expr_ref_model(self)
        
    def val(self):
        return self.ref()
        