'''
Created on Mar 17, 2020

@author: ballance
'''
from .expr_mode import enter_expr_mode, leave_expr_mode

class GeneratorInt(object):
    
    def __init__(self, facade_obj):
        self.fo = facade_obj
        self.model = None
        self.ctor_level = 0
        self.srcinfo_inst = None
        
    def __enter__(self):
        enter_expr_mode()
        self.ctor_level += 1
        
    def __exit__(self, t, v, tb):
        leave_expr_mode()
        self.ctor_level -= 1
        
