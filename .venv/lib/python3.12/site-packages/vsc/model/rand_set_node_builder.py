'''
Created on Oct 11, 2020

@author: ballance
'''
from vsc.model.constraint_model import ConstraintModel
from vsc.model.enum_field_model import EnumFieldModel
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.model_visitor import ModelVisitor
from vsc.model.rand_set import RandSet


class RandSetNodeBuilder(ModelVisitor):
    
    def __init__(self, btor):
        super().__init__()
        self.btor = btor
        self.phase = 0
        
    def build(self, rs : RandSet):
        self.phase = 0
        for f in rs.fields():
            f.accept(self)
        for c in rs.constraints():
            c.accept(self)
        self.phase = 1
        for c in rs.constraints():
            c.accept(self)
    
    def visit_constraint_stmt_enter(self, c:ConstraintModel):
        from ..visitors.model_pretty_printer import ModelPrettyPrinter
        if self.phase == 1:
            c.build(self.btor)
    
    def visit_scalar_field(self, f:FieldScalarModel):
        if self.phase == 0:
            f.build(self.btor)

    def visit_field_bool(self, f):
        if self.phase == 0:
            f.build(self.btor)
            
    def visit_enum_field(self, f:EnumFieldModel):
        if self.phase == 0:
            f.build(self.btor)
            
    def visit_expr_indexed_fieldref(self, e):
        e.get_target().accept(self)
        
    def visit_expr_fieldref(self, e):
        if self.phase == 0:
            e.fm.accept(self)
        super().visit_expr_fieldref(e)

        