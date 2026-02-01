

# Created on Mar 27, 2020
#
# @author: ballance

from typing import Set, List

from vsc.model.field_model import FieldModel
from vsc.model.rand_gen_data import RandGenData
from vsc.model.value_enum import ValueEnum
from vsc.model.field_scalar_model import FieldScalarModel


class EnumFieldModel(FieldScalarModel):
    
    def __init__(self,
                 name : str,
                 enums : List[int],
                 is_rand : bool):
        super().__init__(
            name,
            32,
            True,
            is_rand,
            None)
        self.enums = enums
        self.val = ValueEnum(enums[0])
        
    def accept(self, v):
        v.visit_enum_field(self)
        
    def build(self, btor):
        super().build(btor)
        
        if self.is_used_rand:
            c = None
            for e in self.enums:
                if c is None:
                    c = btor.Eq(
                    self.var,
                    btor.Const(e, self.width))
                else:
                    c = btor.Or(
                        c,
                        btor.Eq(
                            self.var,
                            btor.Const(e, self.width)))
            btor.Assert(c)
            
        return self.var
    
#    def set_val(self, val):
#        self.val.v = val
