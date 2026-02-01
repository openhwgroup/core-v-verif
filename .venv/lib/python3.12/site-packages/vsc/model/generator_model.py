

# Created on Mar 17, 2020
#
# @author: ballance

from vsc.model.field_composite_model import FieldCompositeModel
from typing import List

class GeneratorModel(FieldCompositeModel):
    
    def __init__(self, name):
        super().__init__(name)
        self.covergroup_l : List['Covergroup'] = []
        pass
    
    def add_covergroup(self, cg):
        self.covergroup_l.append(cg)

    def finalize(self):
        super().finalize()
        
        for cg in self.covergroup_l:
            cg.finalize()
            
    def accept(self, v):
        v.visit_generator(self)
        
        
    