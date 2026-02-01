'''
Created on Aug 22, 2020

@author: ballance
'''
from vsc.model.constraint_model import ConstraintModel

class ConstraintSolveOrderModel(ConstraintModel):
    
    def __init__(self,
                 before_l,
                 after_l):
        self.before_l = before_l
        self.after_l = after_l
        
    def accept(self, v):
        v.visit_constraint_solve_order(self)
        