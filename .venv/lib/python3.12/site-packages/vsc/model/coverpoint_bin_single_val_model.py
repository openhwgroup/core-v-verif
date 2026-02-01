

# Created on Mar 20, 2020
#
# @author: ballance

from vsc.model.bin_expr_type import BinExprType
from vsc.model.coverpoint_bin_model_base import CoverpointBinModelBase
from vsc.model.expr_bin_model import ExprBinModel
from vsc.model.expr_literal_model import ExprLiteralModel
from vsc.model.rangelist_model import RangelistModel


class CoverpointBinSingleValModel(CoverpointBinModelBase):
    
    def __init__(self, name, target_val : int):
        super().__init__(name)
        self.target_val = target_val
        self.n_bins = 1
        
    def finalize(self, bin_idx_base:int)->int:
        super().finalize(bin_idx_base)
        return 1
    
    def get_bin_expr(self, bin_idx):
        """Builds expressions to represent the values in this bin"""
        expr = ExprBinModel(
                self.cp.target,
                BinExprType.Eq,
                ExprLiteralModel(self.target_val, False, 32)
                )

        return expr
    
    def get_bin_name(self, bin_idx):
        return self.name 
    
    def sample(self):
        val = self.cp.get_val()
        if val == self.target_val:
            self.hit_bin_idx = 0
            self.cp.coverage_ev(
                self.bin_idx_base,
                self.bin_type)
        else:
            self.hit_bin_idx = -1
            
        return self.hit_bin_idx
    
    def get_bin_range(self, idx):
        print("get_bin_range: " + str(idx))
        return RangelistModel([self.target_val])

    def accept(self, v):
        v.visit_coverpoint_bin_single(self)
        
    def equals(self, oth)->bool:
        eq = isinstance(oth, CoverpointBinSingleValModel)
        
        if eq:
            eq &= self.target_val == oth.target_val
            
        return eq
    
    def clone(self)->'CoverpointBinSingleValModel':
        ret = CoverpointBinSingleValModel(self.name, self.target_val)
        ret.srcinfo_decl = None if self.srcinfo_decl is None else self.srcinfo_decl.clone()
        
        return ret
        
    