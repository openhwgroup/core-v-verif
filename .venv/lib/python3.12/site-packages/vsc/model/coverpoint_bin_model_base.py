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

# Created on Aug 4, 2019
#
# @author: ballance


from enum import Enum, auto

from vsc.model.coverpoint_model import CoverpointModel
from vsc.model.coverpoint_bin_type import CoverpointBinType


class CoverpointBinModelBase(object):
    
    def __init__(self, name):
        self.parent = None
        self.name = name
        self.cp = None
        self.bin_idx_base = -1
        self.hit_bin_idx = -1
        self.n_bins = -1
        self.bin_type = CoverpointBinType.Bins
        
        self.srcinfo_decl = None

    def finalize(self, bin_idx_base:int)->int:
        """Accepts the bin index where this bin starts ; returns number of bins"""
        cp = self.parent
        while cp is not None and not isinstance(cp, CoverpointModel):
            cp = cp.parent
        self.cp = cp
        
        self.bin_idx_base = bin_idx_base
        
        return 0
    
    def get_bin_expr(self, idx):
        raise NotImplementedError()
    
    def get_bin_name(self, bin_idx):
        raise NotImplementedError()
    
    def sample(self):
        raise NotImplementedError("sample not implemented for " + str(type(self)))
                
    def get_n_bins(self):
        return self.n_bins
    
    def hit_idx(self):
        return self.hit_bin_idx

    def set_bin_type(self, bin_type):
        self.bin_type = bin_type
    
    def equals(self, oth):
        eq = isinstance(oth, CoverpointBinModelBase)
        
        if eq:
            eq &= self.name == oth.name
        
        return eq
