'''
Created on Jun 2, 2020

@author: ballance
'''
from vsc.model.variable_bound_model import VariableBoundModel
from vsc.model.field_scalar_model import FieldScalarModel

class VariableBoundScalarModel(VariableBoundModel):
    
    def __init__(self, var : FieldScalarModel):
        super().__init__(var)
        
        # Fill in base domain information
        if var.is_signed:
            self.domain.add_range(-(1 << var.width-1), (1 << var.width-1)-1)
        else:
            self.domain.add_range(0, (1 << var.width)-1)
