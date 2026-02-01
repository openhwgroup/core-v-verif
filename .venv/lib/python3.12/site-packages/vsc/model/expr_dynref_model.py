

# Created on Mar 26, 2020
#
# @author: ballance

from pyboolector import BoolectorNode

from vsc.model.constraint_block_model import ConstraintBlockModel
from vsc.model.expr_model import ExprModel


class ExprDynRefModel(ExprModel):
    """Constraint that is a reference to a dynamic-constraint block"""
    
    def __init__(self, c : ConstraintBlockModel):
        super().__init__()
        self.c = c
        
    def build(self, btor, ctx_width=-1)->BoolectorNode:
        return self.c.build(btor)
        
    def accept(self, v):
        v.visit_constraint_dynref(self)
        
    def width(self):
        return 1
    
    def is_signed(self):
        return False
    
    def __str__(self):
        return "ExprDynRefModel(" + self.c.name + ")"