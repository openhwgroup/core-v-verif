# Licensed to the Apache Software Foundation (ASF) under one
# or more contributor license agreements.  See the NOTICE file
# distributed with this work for additional information
# regarding copyright ownership.  The ASF licenses this file
# to you under the Apache License, Version 2.0 (the
# "License"); you may not use this file except in compliance
# with the License.  You may obtain a copy of the License at
#
#  http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing,
# software distributed under the License is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
# KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations
# under the License.


# Created on Aug 3, 2019
#
# @author: ballance


from vsc.model.coverpoint_model import CoverpointModel
from vsc.model.expr_bin_model import ExprBinModel
from vsc.model.bin_expr_type import BinExprType
from vsc.model.expr_literal_model import ExprLiteralModel


from vsc.model.coverpoint_bin_model_base import CoverpointBinModelBase

class CoverpointBinArrayModel(CoverpointBinModelBase):
    
    def __init__(self, name, low, high):
        super().__init__(name)
        self.low = low 
        self.high = high 
        self.hit_bin_idx = -1
        
    def finalize(self, bin_idx_base:int)->int:
        super().finalize(bin_idx_base)
        return (self.high-self.low+1)
        
    def get_bin_expr(self, idx):
        """Builds expressions to represent a single bin"""
        return ExprBinModel(
            self.cp.target,
            BinExprType.Eq,
            ExprLiteralModel(self.low+idx, False, 32)
        )
    
    def get_bin_name(self, bin_idx):
        return self.name + "[" + str(self.bin_idx_base+bin_idx) + "]"
            
    def sample(self):
        # Query value from the actual coverpoint or expression
        val = int(self.cp.get_val())
        if val >= self.low and val <= self.high:
            # Notify that coverage has changed
            self.cp.coverage_ev(
                self.bin_idx_base+(val-self.low), 
                self.bin_type)
            self.hit_bin_idx = val-self.low
        else:
            self.hit_bin_idx = -1
            
        return self.hit_bin_idx
            
    def dump(self, ind=""):
#        for i in range(self.high-self.low+1):
#            print(ind + self.name + "[" + str(self.low+i) + "]=" + str(self.hit_list[i]))
        pass
    
    def get_bin_range(self, bin_idx):
        print("get_bin_range: " + str(bin_idx))
            
    def get_n_bins(self):
        return (self.high-self.low+1)
    
    def hit_idx(self):
        return self.hit_bin_idx    
    
    def accept(self, v):
        v.visit_coverpoint_bin_array(self)

    def equals(self, oth):
        eq = isinstance(oth, CoverpointBinArrayModel)
        
        if eq:
            eq &= super().equals(oth)
            eq &= self.low == oth.low 
            eq &= self.high == oth.high 
            
        return eq

    def clone(self)->'CoverpointBinArrayModel':
        ret = CoverpointBinArrayModel(self.name, self.low, self.high)
        ret.srcinfo_decl = None if self.srcinfo_decl is None else self.srcinfo_decl.clone()
        
        return ret
    
