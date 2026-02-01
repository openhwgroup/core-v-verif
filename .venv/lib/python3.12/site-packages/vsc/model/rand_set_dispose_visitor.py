'''
Created on Oct 11, 2020

@author: ballance
'''
from vsc.model.constraint_model import ConstraintModel
from vsc.model.enum_field_model import EnumFieldModel
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.model_visitor import ModelVisitor
from vsc.model.rand_set import RandSet


class RandSetDisposeVisitor(ModelVisitor):
    
    def __init__(self):
        super().__init__()
        
    def dispose(self, rs : RandSet):
        for f in rs.fields():
            f.accept(self)
        for c in rs.constraints():
            c.accept(self)
            
    def visit_scalar_field(self, f:FieldScalarModel):
        f.dispose()
        
    def visit_enum_field(self, f:EnumFieldModel):
        f.dispose()
        
    def visit_field_bool(self, f):
        f.dispose()
        
    def visit_constraint_stmt_enter(self, c:ConstraintModel):
        c.dispose()
        
    def visit_expr_indexed_fieldref(self, e):
        e.get_target().accept(self)
        
    def visit_expr_fieldref(self, e):
        e.fm.accept(self)
        