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


# Created on Aug 6, 2019
#
# @author: ballance

from vsc.model.coverpoint_bin_model_base import CoverpointBinModelBase
from vsc.model.rangelist_model import RangelistModel
from vsc.model.coverpoint_bin_single_val_model import CoverpointBinSingleValModel
from vsc.model.coverpoint_bin_single_range_model import CoverpointBinSingleRangeModel
from vsc.model.coverpoint_bin_single_bag_model import CoverpointBinSingleBagModel
from vsc.model.coverpoint_bin_array_model import CoverpointBinArrayModel


class CoverpointBinCollectionModel(CoverpointBinModelBase):
    
    DEBUG_EN = False
    
    def __init__(self, name):
        super().__init__(name)
        self.bin_l = []
        self.hit_bin_idx = -1
        self.n_bins = 0
        
    def finalize(self, bin_idx_base:int)->int:
        super().finalize(bin_idx_base)
#        self.n_bins = reduce(lambda x,y: x+y, map(lambda b: b.get_n_bins(), self.bin_l))
        for b in self.bin_l:
            self.n_bins += b.finalize(self.bin_idx_base+self.n_bins)
        
        return self.n_bins
            
    def get_bin_expr(self, idx):
        """Builds expressions to represent the values in this bin"""
        b = None
        for i in range(len(self.bin_l)):
            b = self.bin_l[i]
            if b.get_n_bins() > idx:
                break;
            idx -= b.get_n_bins()
            
        return b.get_bin_expr(idx)
    
    def get_bin_name(self, idx):
        b = None
        for i in range(len(self.bin_l)):
            b = self.bin_l[i]
            if b.get_n_bins() > idx:
                break;
            idx -= b.get_n_bins()
            
        return b.get_bin_name(idx)        
    
    def add_bin(self, bin_m)->CoverpointBinModelBase:
        bin_m.parent = self
        self.bin_l.append(bin_m)
        return bin_m
        
    def get_coverage(self):
        coverage = 0.0
        
        for bin in self.bin_l:
            coverage += bin.get_coverage()
            
#        coverage /= len(self.bin_l)
        
        return coverage
        
    def sample(self):
        self.hit_bin_idx = -1

        bin_offset = 0
        for b in self.bin_l:
            b.sample()
            if b.hit_bin_idx != -1:
                self.hit_bin_idx = bin_offset + b.hit_bin_idx
            bin_offset += b.get_n_bins()
                
        return self.hit_bin_idx
            
    def get_bin_range(self, idx):
        print("get_bin_range: " + str(idx))
        b = None
        for i in range(len(self.bin_l)):
            b = self.bin_l[i]
            if b.get_n_bins() > idx:
                break;
            idx -= b.get_n_bins()
            
        return b.get_bin_range(idx)

    def dump(self, ind=""):
        print(ind + "Bins " + self.name)
        for b in self.bin_l:
            b.dump(ind + "    ")
            
    def get_hits(self, idx):
        b = None
        for i in range(len(self.bin_l)):
            b = self.bin_l[i]
            if b.get_n_bins() > idx:
                break;
            idx -= b.get_n_bins()
            
        return b.get_hits(idx)
        
    def get_n_bins(self):
        return self.n_bins
    
    def hit_idx(self):
        return self.hit_bin_idx
    
    def set_bin_type(self, bin_type):
        self.bin_type = bin_type
        for b in self.bin_l:
            b.set_bin_type(bin_type)
    
    def accept(self, v):
        v.visit_coverpoint_bin_collection(self)

    def equals(self, oth)->bool:
        eq = isinstance(oth, CoverpointBinCollectionModel)
        
        if eq:
            eq &= super().equals(oth)
            
            if len(self.bin_l) == len(oth.bin_l):
                for i in range(len(self.bin_l)):
                    eq &= self.bin_l[i].equals(oth.bin_l[i])
            
        return eq
    
    def clone(self)->'CoverpointBinCollectionModel':
        ret = CoverpointBinCollectionModel(self.name)
        ret.srcinfo_decl = None if self.srcinfo_decl is None else self.srcinfo_decl.clone()
        
        for bn in self.bin_l:
            ret.add_bin(bn.clone())

        return ret

    @staticmethod    
    def mk_collection(name : str, rangelist : RangelistModel, n_bins)->'CoverpointBinCollectionModel':
        """Creates a bin collection by partitioning a rangelist"""
        n_values = 0
        for r in rangelist.range_l:
            if r[0] == r[1]:
                n_values += 1
            else:
                n_values += (r[1]-r[0]+1)
                
        idx = 0
        
        if CoverpointBinCollectionModel.DEBUG_EN:
            print("--> mk_collection: %d bins ; %d values" % (n_bins, n_values))
            
        ret = CoverpointBinCollectionModel(name)
        if n_bins < n_values:
            # We need to partition the values into bins
            values_per_bin = int(n_values/n_bins)
            have_leftover  = ((n_values%n_bins) != 0)
            r = None
            
            if CoverpointBinCollectionModel.DEBUG_EN:
                print("  Must partition into %d values per bin" % values_per_bin)

            rng_i = 0
            for bin_i in range(n_bins):
#                print("bin_i: " + str(bin_i))
                if r is None:
                    r = rangelist.range_l[rng_i]
#                print("r=" + str(r[0]) + ".." + str(r[1]))
                    
                # If the bin fits within this interval, then just 
                # create a range bin
                if (r[1]-r[0]+1) >= values_per_bin:
                    if CoverpointBinCollectionModel.DEBUG_EN:
                        print("Bin %d..%d is >= values_per_bin ; create bin %d..%d" % (
                            r[0], r[1], r[0], r[0]+values_per_bin-1))

                    if bin_i+1 < n_bins or not have_leftover:                        
                        ret.add_bin(CoverpointBinSingleRangeModel(
                            name + "[" + str(idx) + "]", 
                            r[0], r[0]+values_per_bin-1))
                    else:
                        # When we have leftovers, ensure that the last
                        # bin is a collection
                        b = ret.add_bin(CoverpointBinSingleBagModel(
                            name + "[" + str(idx) + "]"))
                        b.binspec.add_range(r[0], r[1])
                    idx += 1

                    if ((r[1]-r[0]+1) > values_per_bin):
                        # We need to continue working on this range
                        if CoverpointBinCollectionModel.DEBUG_EN:
                            print("Still space in interval. Adjust to %d..%d" % (
                                r[0]+values_per_bin, r[1]))
                        r = r.copy()
                        r[0] += values_per_bin
                    else:
                        # We need to move to the next range
                        r = None
                        rng_i += 1
                else:
                    # The number of values here is smaller than the bin size
                    # We need to start a bin and move forward until we've
                    # collected enough values
                        
                    b = ret.add_bin(CoverpointBinSingleBagModel(name + "[" + str(idx) + "]"))
                    idx += 1
                    
                    b.binspec.add_range(r[0], r[1])
                    n_remaining = values_per_bin - (r[1]-r[0]+1)
                    if CoverpointBinCollectionModel.DEBUG_EN:
                        print("Too few values leftover to fill a bin: (%d..%d) remaining=%d" % (
                            r[0], r[1], n_remaining))
                    r = None
                    rng_i += 1
                    
#                    print("n_remaining=" + str(n_remaining) + " values_per_bin=" + str(values_per_bin))
                    
                    while n_remaining > 0:
                        if r is None:
                            r = rangelist.range_l[rng_i]
                            
                        if (r[1]-r[0]) < n_remaining:
                            # This range is smaller than the remaining bin space
                            b.binspec.add_range(r[0], r[1])
                            n_remaining -= (r[1]-r[0]+1)
                            r = None
                            rng_i += 1
                        else:
                            # This range is larger than the remaining bin space
                            b.binspec.add_range(r[0], r[0]+n_remaining-1)
                            r = r.copy()
                            r[0] += n_remaining
                            n_remaining = 0

            if r is not None:
                # Extend the last bin range
                 
                if CoverpointBinCollectionModel.DEBUG_EN:
                    print("[1] Add leftover range %d..%d" % (r[0], r[1]))
                    
                if r[0] == r[1]:
                    ret.bin_l[-1].binspec.add_value(r[0])
                else:
                    ret.bin_l[-1].binspec.add_range(r[0], r[1])
                rng_i += 1
                
            while rng_i < len(rangelist.range_l):
                r = rangelist.range_l[rng_i]
                if CoverpointBinCollectionModel.DEBUG_EN:
                    print("[2] Add leftover range %d..%d" % (r[0], r[1]))
                if r[0] == r[1]:
                    ret.bin_l[-1].binspec.add_value(r[0])
                else:
                    ret.bin_l[-1].binspec.add_range(r[0], r[1])
                rng_i += 1
        else:
            # We don't actually need to partition
            for r in rangelist.range_l:
                if r[0] == r[1]:
                    ret.add_bin(CoverpointBinSingleValModel(name + "[" + str(idx) + "]", r[0]))
                else:
                    ret.add_bin(CoverpointBinArrayModel(name, r[0], r[1]))
                idx += 1
                    
        return ret
