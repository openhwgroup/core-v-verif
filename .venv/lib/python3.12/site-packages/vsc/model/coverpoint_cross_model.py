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


import random
from typing import Set, Tuple, List

from vsc.model.coveritem_base import CoverItemBase
from vsc.model.expr_model import ExprModel
from vsc.model.rand_if import RandIF
from vsc.model.expr_bin_model import ExprBinModel
from vsc.model.bin_expr_type import BinExprType


class CoverpointCrossModel(CoverItemBase):
    
    def __init__(self, name, options, iff=None):
        super().__init__()
        self.parent = None
        self.name = name
        self.iff = iff
        self.iff_val_cache = True
        self.coverpoint_model_l = []
        self.finalized = False
        self.n_bins = 0

        # Need to map (tuple)->bin_idx (for coverage recording)
        # Need to map bin_idx->(tuple) (for constraint driving)
        # Need to track unhit bin indexes
        self.hit_l : List[int] = []
        self.tuple2idx_m : Dict[Tuple,int] = {}
        self.idx2tuple_m : Dict[int,Tuple] = {}
        self.unhit_s : Set[Tuple] = set()
        
        self.srcinfo_decl = None
        self.coverage = 0.0
        self.coverage_calc_valid = False
        self.options = options

    def coverpoints(self):
        return self.coverpoint_model_l
        
    def get_coverage(self):
        if not self.coverage_calc_valid:
            self.coverage = (len(self.hit_l)-len(self.unhit_s))/len(self.hit_l) * 100.0
            self.coverage_calc_valid = True
            
        return self.coverage
    
    def get_n_bins(self):
        return self.n_bins
    
    def get_bin_expr(self, bin_idx:int)->ExprModel:
        ret = None
        
        key_t = self.idx2tuple_m[bin_idx]
        
        for i in range(len(self.coverpoint_model_l)):
            cp_expr = self.coverpoint_model_l[i].get_bin_expr(key_t[i])
            
            ret = cp_expr if ret is None else ExprBinModel(
                ret,
                BinExprType.And,
                cp_expr)
            
        return ret
    
    def select_unhit_bin(self, r:RandIF)->int:
        if len(self.unhit_s) > 0:
            return random.sample(self.unhit_s, 1)[0]
        else:
            return -1

    def get_bin_hits(self, bin_idx):
        return self.hit_l[bin_idx]
            
    def get_bin_name(self, bin_idx)->str:
        t = self.idx2tuple_m[bin_idx]
        ret = "<"
        for i in range(len(t)):
            idx = t[i]
            if i > 0:
                ret += ","
            ret += self.coverpoint_model_l[i].get_bin_name(idx)
        ret += ">"
        return ret
    
    def add_coverpoint(self, cp_m):
        self.coverpoint_model_l.append(cp_m)
    
    def finalize(self):
        if not self.finalized:
            self._build_hit_map(0, [])
            
            self.hit_l = [0]*self.n_bins
        self.finalized = True
    
    def accept(self, v):
        v.visit_coverpoint_cross(self)
    
    def _build_hit_map(self, i, key_m):
        for bin_i in range(self.coverpoint_model_l[i].get_n_bins()):
            key_m.append(bin_i)
            
            if i+1 >= len(self.coverpoint_model_l):
                key = tuple(key_m)
                # Reached the bottom of the list
#                print("Tuple: " + str(key))
                self.tuple2idx_m[key] = self.n_bins
                self.idx2tuple_m[self.n_bins] = key
                self.unhit_s.add(self.n_bins)
                self.n_bins += 1
            else:
                self._build_hit_map(i+1, key_m)
                
            key_m.pop()
    
    def sample(self):
        if not self.finalized:
            raise Exception("Cross sampled before finalization")
        
        if self.iff is not None:
            self.iff_val_cache = bool(self.iff.val())
        
        have_cp_hit = self.iff_val_cache
        key_m = []
        if have_cp_hit:
            for cp in self.coverpoint_model_l:
                have_bin_hit = False
                if cp.iff_val_cache:
                    idx = 0
                    for b in cp.bin_model_l:
                        if b.hit_idx() != -1:
                            key_m.append(b.hit_idx() + idx)
                            have_bin_hit = True
                            break
                        else:
                            idx += b.get_n_bins()
                    
                    if have_bin_hit:
                        have_cp_hit = True
                    else:
                        have_cp_hit = False
                        break
                else:
                    have_cp_hit = False
                    break
            
        if have_cp_hit:
            key = tuple(key_m)
            bin_idx = self.tuple2idx_m[key]
            self.hit_l[bin_idx] += 1
            if bin_idx in self.unhit_s:
                # New bin hit
                self.parent.coverage_ev(self, bin_idx)
                self.unhit_s.remove(bin_idx)
                self.coverage_calc_valid = False

    def dump(self, ind=""):
        print(ind + "Cross: " + self.name)
        for i,count in enumerate(self.hit_l):
            print(ind + "    " + str(i) + "=" + str(count))
            
    def equals(self, oth : 'CoverpointCrossModel')->bool:
        eq = True
        
        if len(self.coverpoint_model_l) == len(oth.coverpoint_model_l):
            for i in range(len(self.coverpoint_model_l)):
                eq &= self.coverpoint_model_l[i].equals(oth.coverpoint_model_l[i])
        else:
            eq = False
            
        return eq

    def clone(self, coverpoint_m)->'CoverpointCrossModel':
        ret = CoverpointCrossModel(self.name, self.options.clone())
        ret.srcinfo_decl = None if self.srcinfo_decl is None else self.srcinfo_decl.clone()
        
        for cp in self.coverpoint_model_l:
            ret.add_coverpoint(coverpoint_m[cp])
        
        return ret