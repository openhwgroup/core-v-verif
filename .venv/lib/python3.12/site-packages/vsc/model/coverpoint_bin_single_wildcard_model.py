'''
Created on Jul 23, 2021

@author: mballance
'''
from vsc.model.coverpoint_bin_model_base import CoverpointBinModelBase
from vsc.model.wildcard_binspec import WildcardBinspec

class CoverpointBinSingleWildcardModel(CoverpointBinModelBase):
    
    def __init__(self, name, specs : WildcardBinspec):
        super().__init__(name)
        self.n_bins = 1
        self.wildcard_binspec = specs
        pass
    
    def finalize(self, bin_idx_base : int) -> int:
        super().finalize(bin_idx_base)
        return 1
    
    def get_bin_expr(self, bin_idx):
        pass
    
    def get_bin_name(self, bin_idx):
        return self.name
    
    def sample(self):
        val = int(self.cp.get_val())

        # Process each value/mask pair
        self.hit_bin_idx = -1        
        for s in self.wildcard_binspec.specs:
            if (val & s[1]) == s[0]:
                self.hit_bin_idx = 0
                self.cp.coverage_ev(
                    self.bin_idx_base,
                    self.bin_type)
                break
        
        
    def accept(self, v):
        v.visit_coverpoint_bin_single_wildcard(self)
        
    def equals(self, oth) -> bool:
        eq = isinstance(oth, CoverpointBinSingleWildcardModel)
        
        if eq:
            eq &= self.wildcard_binspec.equals(oth.wildcard_binspec)
            
        return eq
    
    def clone(self):
        return CoverpointBinSingleWildcardModel(
            self.name, 
            self.wildcard_binspec.clone())
