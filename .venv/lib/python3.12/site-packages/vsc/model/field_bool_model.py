'''
Created on May 16, 2020

@author: ballance
'''
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.value import Value
from vsc.model.value_bool import ValueBool


class FieldBoolModel(FieldScalarModel):
    
    def __init__(self, name, is_rand):
        super().__init__(name, 1, 0, is_rand)
        
    def accept(self, v):
        v.visit_bool_field(self)

    def get_val(self):
        return ValueBool(bool(self.val))
    
    def set_val(self, val:Value):
        self.val.v = 1 if bool(val) else 0
    