'''
Created on Jul 5, 2021

@author: mballance
'''
from vsc.model.expr_array_subscript_model import ExprArraySubscriptModel
from vsc.model.expr_indexed_field_ref_model import ExprIndexedFieldRefModel
from vsc.model.field_array_model import FieldArrayModel
from vsc.model.model_visitor import ModelVisitor


class Expr2FieldTypeVisitor(ModelVisitor):
    """Traverses an array-reference expression, returning element-type information"""
    
    DEBUG_EN = False
    
    def __init__(self):
        super().__init__()
        self.type = None
        self.field = None
        pass
    
    def fieldtype(self, e):
        self.type = None
        e.accept(self)
        return self.type
    
    def visit_expr_fieldref(self, e):
        if Expr2FieldTypeVisitor.DEBUG_EN:
            print("--> visit_expr_fieldref")
        self.field = e.fm
        self.field.accept(self)
        if Expr2FieldTypeVisitor.DEBUG_EN:
            print("<-- visit_expr_fieldref")
            
    def visit_field_scalar_array(self, f:FieldArrayModel):
        if Expr2FieldTypeVisitor.DEBUG_EN:
            print("--> visit_field_array")
        self.type = f.type_t
        if Expr2FieldTypeVisitor.DEBUG_EN:
            print("--> visit_field_array fm=%s ft=%s" % (str(self.field), str(self.type)))
        
    def visit_expr_indexed_fieldref(self, e : ExprIndexedFieldRefModel):
        if Expr2FieldTypeVisitor.DEBUG_EN:
            print("--> visit_expr_indexed_fieldref")
        e.root.accept(self)
        if Expr2FieldTypeVisitor.DEBUG_EN:
            print("<-- visit_expr_indexed_fieldref fm=%s ft=%s" % (str(self.field), str(self.type)))
        
    def visit_expr_array_subscript(self, s : ExprArraySubscriptModel):
        if Expr2FieldTypeVisitor.DEBUG_EN:
            print("--> visit_expr_array_subscript")
        s.lhs.accept(self)

        if Expr2FieldTypeVisitor.DEBUG_EN:
            print("<-- visit_expr_array_subscript")
        