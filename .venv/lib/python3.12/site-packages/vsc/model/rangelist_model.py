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
from typing import List




# Created on Aug 4, 2019
#
# @author: ballance


class RangelistModel(object):
    
    def __init__(self, rl : List[List[int]]=None):
        self.range_l = []

        if rl is not None:
            for r in rl:
                if isinstance(r, (list,tuple)):
                    if len(r) == 2:
                        self.range_l.append([r[0], r[1]])
                    else:
                        raise Exception("Each range element must have 2 elements")
                else:
                    self.range_l.append([int(r), int(r)])
   
                    
    def add_value(self, v):
        self.range_l.append([v,v])

    def add_range(self, low, high):
        self.range_l.append([low, high])

    # Merge any overlapping ranges        
    def compact(self):
        self.range_l.sort(key=lambda e : e[0])
        
        i=0
        while i < len(self.range_l)-1:
            if self.range_l[i][0] >= self.range_l[i+1][0]:
                # Entire range subsumed
                self.range_l.pop(i)
            elif self.range_l[i][1] >= self.range_l[i+1][1]:
                # Upper just overlaps
                self.range_l[i][1] = self.range_l[i+1][0]
                self.range_l.pop(i+1)
            else:
                i += 1
        pass
    
    def intersect(self, other):
        """
        Intersects another list or ranges with this one,
        trimming values that overlap
        """

        if len(self.range_l) == 0 or len(other.range_l) == 0:
            return
        
        rng_i=0
        while rng_i < len(self.range_l):
            for r in other.range_l:
                rng_i = self._intersect(
                    self.range_l,
                    rng_i,
                    self.range_l[rng_i],
                    r)
            rng_i += 1
    
    def _intersect(self,
                   ranges,
                   rng_i,
                   target_rng,
                   trim_rng) -> int:
        
        if target_rng[0] >= trim_rng[0] and target_rng[1] <= trim_rng[1]:
            # The target range is entirely inside the trim range
            ranges.pop(rng_i)
            rng_i -= 1
        elif trim_rng[0] > target_rng[0] and trim_rng[1] < target_rng[1]:
            # Trim range is entirely inside the target range
            # Need to split the range into two
            new_rng = [trim_rng[1]+1, target_rng[1]]
            target_rng[1] = trim_rng[0]-1
            ranges.insert(rng_i+1, new_rng)
        elif trim_rng[0] > target_rng[0] and trim_rng[0] <= target_rng[1]:
            # Lower edge of the trim bin inside the target range, but
            # doesn't eclipse the entire range
            target_rng[1] = trim_rng[0]-1
        elif trim_rng[1] >= target_rng[0] and trim_rng[1] < target_rng[1]:
            # Upper edge of the trim bin is inside the target range, but
            # doesn't eclipse it
            target_rng[0] = trim_rng[1]+1
            
        return rng_i
        
    def __contains__(self, val):
        for r in self.range_l:
            if val >= r[0] and val <= r[1]:
                return True
            
        return False
    
    def equals(self, oth)->bool:
        eq = isinstance(oth, RangelistModel)

        if len(self.range_l) == len(oth.range_l):
            for i in range(len(self.range_l)):
                eq &= self.range_l[i][0] == oth.range_l[i][0]
                eq &= self.range_l[i][1] == oth.range_l[i][1]
        else:
            eq = False
            
        return eq
    
    def toString(self):
        ret = "["
        for i,r in enumerate(self.range_l):
            if i > 0:
                ret += ","
            ret += str(r[0]) + ".." + str(r[1])
        ret += "]"
        
        return ret
            

    def clone(self):
        ret = RangelistModel(None)
        
        for r in self.range_l:
            ret.range_l.append([r[0], r[1]])
            
        return ret
    
    def accept(self, v):
        v.visit_rangelist(self);