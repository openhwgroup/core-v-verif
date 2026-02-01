'''
Created on May 30, 2020

@author: ballance
'''
from vsc.model.field_scalar_model import FieldScalarModel
from vsc.model.rangelist_model import RangelistModel
from vsc.model.variable_bound_propagator import VariableBoundPropagator
from typing import List

class VariableBoundModel(object):
    
    def __init__(self, var : FieldScalarModel):
        self.var = var
        self.domain : RangelistModel = RangelistModel()
        self.propagators : List[VariableBoundPropagator] = []
        self.domain_sz = -1
        self.domain_offsets = []
        # Whether this field is referenced by a constraint
        self.constrained = False

    def isEmpty(self):
        if len(self.domain.range_l) == 0:
            return True
        elif len(self.domain.range_l) == 1 and (self.domain.range_l[0][1]-self.domain.range_l[0][0]) == 0:
            return True
        else:
            return False
            
    def add_propagator(self, p):
        if p is None:
            raise Exception("Adding null propagator")
        self.propagators.append(p)
        
    def update(self):
        """Called to update quantities calculated from the domain"""
        self.domain_sz = 0
        self.domain_offsets.clear()
        for r in self.domain.range_l:
            self.domain_sz += (r[1]-r[0])+1
            self.domain_offsets.append(self.domain_sz)

    def offset2value(self, off):
        i=0
        if off < self.domain_offsets[0]:
            return self.domain.range_l[i][0]
        else:
            while i < len(self.domain_offsets):
                if (i+1 < len(self.domain_offsets) and self.domain_offsets[i+1] > off):
                    break
                i += 1

            return self.domain.range_l[i+1][0]+(off-self.domain_offsets[i])

    def propagate(self):
        for p in self.propagators:
            p.propagate()
            
    def toString(self):
        ret = self.var.name
        
        for i,r in enumerate(self.domain.range_l):
            if i > 0:
                ret += " "
            ret += "[" + str(r[0]) + ".." + str(r[1]) + "]"
        
        return ret
            
    