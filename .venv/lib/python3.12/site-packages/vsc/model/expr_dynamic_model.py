'''
Created on Aug 21, 2020

@author: ballance
'''
from vsc.model.expr_model import ExprModel

class ExprDynamicModel(ExprModel):
    '''Base class for expressions that must be computed dynamically'''
    
    def __init__(self):
        self.cached_expr = None
        self.cached_node = None
        pass
   
    def reset(self):
        self.cached_expr = None
        self.cached_node = None
        
    def expr(self):
        if self.cached_expr is None:
            self.cached_expr = self.build_expr()
        return self.cached_expr
        
    def build(self, btor, ctx_width=-1):
        if self.cached_expr is None:
            self.cached_expr = self.build_expr()
        if self.cached_node is None:
            self.cached_node = self.cached_expr.build(btor)
        return self.cached_node
        
    def build_expr(self):
        raise Exception("Class " + str(type(self)) + " does not implement build_expr")
        
        