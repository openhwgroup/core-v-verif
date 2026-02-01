'''
Created on Mar 14, 2020

@author: ballance
'''
from typing import Dict, List
from vsc.model.covergroup_model import CovergroupModel
from vsc.visitors.model_pretty_printer import ModelPrettyPrinter

class CoverageRegistry(object):
    
    _inst = None
    
    def __init__(self):
        # Map of 'simple' typename to a list of specific covergroup 
        # implementations. Difference parameterizations are named
        # _1, _2, _3, etc
        self.covergroup_type_m : Dict[str, List[CovergroupModel]] = {}
        pass
    
    @staticmethod
    def inst():
        if CoverageRegistry._inst is None:
            CoverageRegistry._inst = CoverageRegistry()
            
        return CoverageRegistry._inst
    
    @staticmethod
    def clear():
        CoverageRegistry._inst = None
    
    def types(self):
        return self.covergroup_type_m.keys()
    
    def instances(self, t):
        return self.covergroup_type_m[t]
    
    def register_cg(self, cg : CovergroupModel):
        cg_t : CovergroupModel = None

        # First, see if there's an existing entry
        if cg.typename in self.covergroup_type_m.keys():
            # Okay, now we need to do some detailed comparison
            # Covergroups with the same base typename can have different
            # content if constructor parameters are used to customize content.
            for cg_c in self.covergroup_type_m[cg.typename]:
                if cg_c.equals(cg):
                    cg_t = cg_c
                    break
                
            if cg_t is None:
                # The new type does not have 
                # Okay, create a clone of the instance and give it a new name
                cg_t = cg.clone()
                # Type covergroups have their coverage data directly provided
                # Clear out the 'target' fields of coverpoints to ensure this happens
                for cp in cg_t.coverpoint_l:
                    cp.target = None
                    
                cg_t.srcinfo_inst = None # Types do not have instance information
                cg_t.finalize()
                self.covergroup_type_m[cg.typename].append(cg_t)
                n_cg = len(self.covergroup_type_m[cg.typename])

                # Base covergroup type is called 'name', while derivatives
                # are labeled _1, _2, _3                
                cg_t.name = cg_t.typename + "_" + str(n_cg)
                
        else:
            # No, nothing here yet. Create a clone of this instance
            # covergroup to use as a covergroup type
            cg_t = cg.clone()
            
            # Type covergroups have their coverage data directly provided
            # Clear out the 'target' fields of coverpoints to ensure this happens
            for cp in cg_t.coverpoint_l:
                cp.target = None

            cg_t.srcinfo_inst = None # Types do not have instance information
            cg_t.finalize()
            self.covergroup_type_m[cg.typename] = [cg_t]
            
        # Hook up the instance to the relevant type covergroup
        cg.type_cg = cg_t
        cg_t.cg_inst_l.append(cg)
        
    def covergroup_types(self):
        ret = []
        for name,cg_l in self.covergroup_type_m.items():
            ret.extend(cg_l)
            
        return ret
        
        
    def accept(self, v):
        for name,cg_l in self.covergroup_type_m.items():
            for cg in cg_l:
                cg.accept(v)
        
    
        
    

    
        
    
    