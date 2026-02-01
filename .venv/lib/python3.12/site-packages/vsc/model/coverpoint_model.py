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

from vsc.model.expr_model import ExprModel
from vsc.model.expr_cond_model import ExprCondModel
from vsc.model.expr_literal_model import ExprLiteralModel
from vsc.model.coveritem_base import CoverItemBase
from vsc.model.rand_if import RandIF
from typing import Set, List, Tuple
import random
from _random import Random
from vsc.model.coverage_options_model import CoverageOptionsModel
from vsc.model.rangelist_model import RangelistModel
from vsc.model.coverpoint_bin_type import CoverpointBinType


# Created on Aug 3, 2019
#
# @author: ballance


class CoverpointModel(CoverItemBase):
    
    def __init__(self, 
                 target : ExprModel, 
                 name : str,
                 options,
                 iff : ExprModel = None):
        super().__init__()
        self.parent = None
        self.target = target
        self.iff = iff

        # Cached value Target-ref field. This is used to retrieve values for
        # type covergroups
        self.iff_val_cache = True
        self.target_val_cache = 0

        self.name = name
        self.n_bins = 0
        self.n_ignore_bins = 0
        self.n_illegal_bins = 0
        self.unhit_s : Set[int] = set()
        self.hit_l : List[int] = []
        self.hit_ignore_l : List[int] = []
        self.hit_illegal_l : List[int] = []
        self.bin_model_l = []
        self.ignore_bin_model_l = []
        self.illegal_bin_model_l = []
        
        self.srcinfo_decl = None
        self.bin_expr = None
        # Tracks 
        self.coverage = 0.0
        self.coverage_calc_valid = False

        if options is None:        
            self.options = CoverageOptionsModel()
        else:
            self.options = options
            
            
    def add_bin_model(self, bin_m):
        bin_m.parent = self
        self.bin_model_l.append(bin_m)
        return bin_m
    
    def add_ignore_bin_model(self, bin_m):
        bin_m.parent = self
        bin_m.set_bin_type(CoverpointBinType.Ignore)
        self.ignore_bin_model_l.append(bin_m)
        return bin_m
    
    def add_illegal_bin_model(self, bin_m):
        bin_m.parent = self
        bin_m.set_bin_type(CoverpointBinType.Illegal)
        self.illegal_bin_model_l.append(bin_m)
        return bin_m
        
    def finalize(self):
        self.n_bins = 0
        self.n_ignore_bins = 0
        self.n_illegal_bins = 0
        
        for b in self.bin_model_l:
            self.n_bins += b.finalize(self.n_bins)
        for b in self.ignore_bin_model_l:
            self.n_ignore_bins += b.finalize(self.n_ignore_bins)
        for b in self.illegal_bin_model_l:
            self.n_illegal_bins += b.finalize(self.n_illegal_bins)
            
        # Track unhit bins within this coverpoint
        self.unhit_s.update(range(self.n_bins))
        self.hit_l = [0]*self.n_bins
        self.hit_ignore_l = [0]*self.n_ignore_bins
        self.hit_illegal_l = [0]*self.n_illegal_bins
            
    def get_bin_expr(self, bin_idx):
        b = None
        
        # First, find the bin this index applies to
        for i in range(len(self.bin_model_l)):
            b = self.bin_model_l[i]
            if b.get_n_bins() > bin_idx:
                break
            bin_idx -= b.get_n_bins()

        # Now, return the actual expression            
        return b.get_bin_expr(bin_idx)
    
    def _get_target_bin(self, bin_idx)->Tuple['CoverpointBinModelBase',int]:
        b = None
        
        # First, find the bin this index applies to
        for i in range(len(self.bin_model_l)):
            b = self.bin_model_l[i]
            if b.get_n_bins() > bin_idx:
                break
            bin_idx -= b.get_n_bins()
        
        return (b,bin_idx)        
    
    def _get_target_ignore_bin(self, bin_idx)->Tuple['CoverpointBinModelBase',int]:
        b = None
        
        # First, find the bin this index applies to
        for i in range(len(self.ignore_bin_model_l)):
            b = self.ignore_bin_model_l[i]
            if b.get_n_bins() > bin_idx:
                break
            bin_idx -= b.get_n_bins()
        
        return (b,bin_idx)        
    
    def _get_target_illegal_bin(self, bin_idx)->Tuple['CoverpointBinModelBase',int]:
        b = None
        
        # First, find the bin this index applies to
        for i in range(len(self.illegal_bin_model_l)):
            b = self.illegal_bin_model_l[i]
            if b.get_n_bins() > bin_idx:
                break
            bin_idx -= b.get_n_bins()
        
        return (b,bin_idx)
    
    def get_coverage(self)->float:
        if not self.coverage_calc_valid:
            self.coverage = (len(self.hit_l)-len(self.unhit_s))/len(self.hit_l) * 100.0
            self.coverage_calc_valid = True
        
        return self.coverage
    
    def get_inst_coverage(self):
        raise Exception("get_inst_coverage unimplemented")
        
    def sample(self):

        if self.iff is not None:
            self.iff_val_cache = bool(self.iff.val())

        if self.iff_val_cache:            
            for b in self.bin_model_l:
                b.sample()
            for b in self.ignore_bin_model_l:
                b.sample()
            for b in self.illegal_bin_model_l:
                b.sample()
            
    def select_unhit_bin(self, r:RandIF)->int:
        if len(self.unhit_s) > 0:
            return r.sample(self.unhit_s,1)[0]
#            return random.sample(self.unhit_s,1)[0]
        else:
            return -1
        
    def get_bin_range(self, bin_idx) -> RangelistModel:
        b,off = self._get_target_bin(bin_idx)
        
        return b.get_bin_range(off)
        pass
            
    def coverage_ev(self, bin_idx, bin_type):
        """Called by a bin to signal that an uncovered bin has been covered"""
        self.coverage_calc_valid = False
        if bin_type == CoverpointBinType.Bins:
            if bin_idx in self.unhit_s:
                self.parent.coverage_ev(self, bin_idx)
                self.unhit_s.remove(bin_idx)
            self.hit_l[bin_idx] += 1
            self.coverage_calc_valid = False
        elif bin_type == CoverpointBinType.Ignore:
            self.hit_ignore_l[bin_idx] += 1
        elif bin_type == CoverpointBinType.Illegal:
            self.hit_illegal_l[bin_idx] += 1
            
    def get_val(self):
        if self.target is not None:
            self.target_val_cache = self.target.val()
        return self.target_val_cache
            
    def accept(self, v):
        v.visit_coverpoint(self)
            
    def dump(self, ind=""):
        print(ind + "Coverpoint: " + self.name)
        for b in self.bin_model_l:
            b.dump(ind + "    ")
            
    def get_n_bins(self):
        return self.n_bins
    
    def get_n_ignore_bins(self):
        return self.n_ignore_bins
    
    def get_n_illegal_bins(self):
        return self.n_illegal_bins
    
    def get_n_hit_bins(self):
        return len(self.hit_l)-len(self.unhit_s)
        
    def get_bin_hits(self, bin_idx):
        return self.hit_l[bin_idx]
    
    def get_ignore_bin_hits(self, bin_idx):
        return self.hit_ignore_l[bin_idx]
    
    def get_illegal_bin_hits(self, bin_idx):
        return self.hit_illegal_l[bin_idx]

    def get_bin_name(self, bin_idx)->str:
        b,idx = self._get_target_bin(bin_idx)
        return b.get_bin_name(idx)
        
    def get_ignore_bin_name(self, bin_idx)->str:
        b,idx = self._get_target_ignore_bin(bin_idx)
        return b.get_bin_name(idx)
    
    def get_illegal_bin_name(self, bin_idx)->str:
        b,idx = self._get_target_illegal_bin(bin_idx)
        return b.get_bin_name(idx)
    
    def get_hit_bins(self, bin_l):
        bin_idx = 0
        for b in self.bin_model_l:
            if b.hit_idx() != -1:
                bin_l.append(bin_idx + b.hit_idx())
            bin_idx += b.n_bins()

    def equals(self, oth:'CoverpointModel')->bool:
        eq = True
        
        eq &= self.name == oth.name
        
        if len(self.bin_model_l) == len(oth.bin_model_l):
            for s,o in zip(self.bin_model_l, oth.bin_model_l):
                eq &= s.equals(o)
        else:
            eq= False
            
        if len(self.ignore_bin_model_l) == len(oth.ignore_bin_model_l):
            for s,o in zip(self.ignore_bin_model_l, oth.ignore_bin_model_l):
                eq &= s.equals(o)
        else:
            eq= False
            
        if len(self.illegal_bin_model_l) == len(oth.illegal_bin_model_l):
            for s,o in zip(self.illegal_bin_model_l, oth.illegal_bin_model_l):
                eq &= s.equals(o)
        else:
            eq= False
            
        return eq
    
    def clone(self)->'CoverpointModel':
        ret = CoverpointModel(self.target, self.name, self.options.clone())
        ret.srcinfo_decl = None if self.srcinfo_decl is None else self.srcinfo_decl.clone()
        
        for bn in self.bin_model_l:
            ret.add_bin_model(bn.clone())
            
        for bn in self.ignore_bin_model_l:
            ret.add_ignore_bin_model(bn.clone())
            
        for bn in self.illegal_bin_model_l:
            ret.add_illegal_bin_model(bn.clone())

        return ret
        
