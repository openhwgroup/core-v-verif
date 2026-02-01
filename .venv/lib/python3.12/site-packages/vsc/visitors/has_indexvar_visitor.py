'''
Created on Jun 7, 2021

@author: mballance
'''
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.model_visitor import ModelVisitor


class HasIndexVarVisitor(ModelVisitor):
    """Used to check whether an index expression references a 
       known foreach-loop variable"""
       
    def __init__(self, index_set):
        super().__init__()
        self.index_set = index_set
        self.ret = False
        
    def has(self, e):
        self.ret = False
        e.accept(self)
        return self.ret
    
    def visit_expr_fieldref(self, e):
        print("HasIndex: fm=" + e.fm.fullname)
        self.ret |= e.fm in self.index_set
    