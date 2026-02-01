'''
Created on Aug 21, 2020

@author: ballance
'''
from vsc.model.expr_dynamic_model import ExprDynamicModel

class ExprArrayProductModel(ExprDynamicModel):
    
    def __init__(self, arr):
        super().__init__()
        self.arr = arr
        
    def is_signed(self):
        return self.arr.is_signed
    
    def width(self):
#        ret = self.arr.width
#        if ret < 32:
#            ret = 32
#        return ret        
        return 64
        
    def build_expr(self):
        return self.arr.get_product_expr()
    
    def build(self, btor, ctx_width=-1):
        return self.arr.build_product_expr(btor, ctx_width);
    
    def accept(self, v):
        v.visit_expr_array_product(self)
    