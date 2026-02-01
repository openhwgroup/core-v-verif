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

from vsc.model.coverpoint_bin_model_base import CoverpointBinModelBase

class CoverpointBinEnumModel(CoverpointBinModelBase):
    
    def __init__(self, name, val):
        super().__init__(name)
        self.target_val = val
        
        self.n_hits = 0
        self.cp = None
        self.n_bins = 1

    def finalize(self, bin_idx_base:int)->int:
        super().finalize(bin_idx_base)
        return 1
    
    def get_bin_name(self, bin_idx):
        return self.name 

    def sample(self):
        # Query value from the actual coverpoint or expression
#        print("sample: binspec=" + str(self.binspec))
        val = self.cp.get_val()
        if int(val) == int(self.target_val):
            self.hit_bin_idx = 0
            self.cp.coverage_ev(
                self.bin_idx_base,
                self.bin_type)
        else:
            self.hit_bin_idx = -1
            
        return self.hit_bin_idx
            
    def accept(self, v):
        v.visit_coverpoint_bin_enum(self)

    def equals(self, oth)->bool:
        eq = isinstance(oth, CoverpointBinEnumModel)
        
        if eq:
            eq &= self.target_val == oth.target_val
            
        return eq
    
    def clone(self)->'CoverpointBinEnumModel':
        ret = CoverpointBinEnumModel(self.name, self.target_val)
        ret.srcinfo_decl = None if self.srcinfo_decl is None else self.srcinfo_decl.clone()
        
        return ret        