

# Created on Mar 20, 2020
#
# @author: ballance

from vsc.model.rand_if import RandIF
from typing import List
from vsc.model.expr_model import ExprModel

class CoverItemBase(object):
    
    def __init__(self):
        super().__init__()
        
    def get_n_bins(self)->int:
        raise NotImplementedError("get_n_bins not implemented by " + str(type(self)))
    
    def get_bin_hits(self, bin_idx)->int:
        raise NotImplementedError("get_bin_hits not implemented by " + str(type(self)))
    
    def get_hit_bins(self)->List[int]:
        raise NotImplementedError("get_hit_bins not implemented by " + str(type(self)))
    
    def get_unhit_bins(self)->List[int]:
        raise NotImplementedError("get_unhit_bins not implemented by " + str(type(self)))
    
    def get_bin_expr(self, bin_idx:int)->ExprModel:
        raise NotImplementedError("get_bin_expr not implemented by " + str(type(self)))
    
    def get_coverage(self)->float:
        raise NotImplementedError("get_coverage not implemented by " + str(type(self)))
    
    def sample(self):
        raise NotImplementedError("sample not implemented by " + str(type(self)))
    
    def select_unhit_bin(self, r:RandIF)->int:
        raise NotImplementedError("select_unhit_bin not implemented by " + str(type(self)))
        