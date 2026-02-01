

# Created on Mar 20, 2020
#
# @author: ballance

from vsc.model.coverpoint_bin_model_base import CoverpointBinModelBase
from vsc.model.expr_bin_model import ExprBinModel
from vsc.model.expr_literal_model import ExprLiteralModel
from vsc.model.bin_expr_type import BinExprType

class CoverpointBinSingleRangeModel(CoverpointBinModelBase):
    
    def __init__(self, 
                 name, 
                 target_val_low : int, 
                 target_val_high : int):
        super().__init__(name)
        self.target_val_low = target_val_low
        self.target_val_high = target_val_high
        self.n_bins = 1
        
    def finalize(self, bin_idx_base:int)->int:
        super().finalize(bin_idx_base)
        return 1
    
    def get_bin_expr(self, bin_idx):
        """Builds expressions to represent the values in this bin"""
        expr = ExprBinModel(
            ExprBinModel(
                self.cp.target,
                BinExprType.Ge,
                ExprLiteralModel(self.target_val_low, False, 32)),
            BinExprType.And,
            ExprBinModel(
                self.cp.target,
                BinExprType.Le,
                ExprLiteralModel(self.target_val_high, False, 32))
            )
        return expr    
    
    def get_bin_name(self, bin_idx):
        return self.name 
    
    def sample(self):
        val = int(self.cp.get_val())
        if val >= self.target_val_low and val <= self.target_val_high:
            self.hit_bin_idx = 0
            self.cp.coverage_ev(
                self.bin_idx_base,
                self.bin_type)
        else:
            self.hit_bin_idx = -1
            
        return self.hit_bin_idx
            
    def accept(self, v):
        v.visit_coverpoint_bin_single_range(self)
        
    def equals(self, oth)->bool:
        eq = isinstance(oth, CoverpointBinSingleRangeModel)
        
        if eq:
            eq &= (self.target_val_low == oth.target_val_low)
            eq &= (self.target_val_high == oth.target_val_high)
            
        return eq
    
    def clone(self)->'CoverpointBinSingleRangeModel':
        ret = CoverpointBinSingleRangeModel(
            self.name, 
            self.target_val_low,
            self.target_val_high)
        ret.srcinfo_decl = None if self.srcinfo_decl is None else self.srcinfo_decl.clone()
        
        return ret
        
    