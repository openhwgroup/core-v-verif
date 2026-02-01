'''
Created on Jun 2, 2020

@author: ballance
'''
from vsc.model.variable_bound_model import VariableBoundModel
from vsc.model.enum_field_model import EnumFieldModel


class VariableBoundEnumModel(VariableBoundModel):
    
    def __init__(self, var : EnumFieldModel):
        super().__init__(var)
        
        for v in var.enums:
            self.domain.add_value(v)
            
        self.domain.range_l.sort(key=lambda e:e[0])
        
