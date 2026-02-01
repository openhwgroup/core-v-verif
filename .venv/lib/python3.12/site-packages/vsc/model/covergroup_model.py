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
from vsc.model.coverpoint_cross_model import CoverpointCrossModel
from vsc.model.field_composite_model import FieldCompositeModel
from vsc.model.coverage_options_model import CoverageOptionsModel

class CovergroupModel(FieldCompositeModel):
    
    def __init__(self, 
                 name:str,
                 options=None):
        super().__init__(name)
        
        # Handle to the type covergroup this instance is associated with
        self.type_cg : CovergroupModel = None
        
        # List of covergroup instances of this type
        self.cg_inst_l : List[CovergroupModel] = []
        
        self.coverpoint_l = []
        self.cross_l = []
        self.typename = name # Typename of this covergroup
        self.du_name = None # Design-unit typename in which this covergroup is instanced
        self.instname = None # Design-unit instance name in which this covergroup is instanced
        
        self.coverage = 0.0
        self.coverage_calc_valid = False

        if options is None:        
            self.options = CoverageOptionsModel()
        else:
            self.options = options
        
        
    def finalize(self):
        for cp in self.coverpoint_l:
            cp.finalize()
            
        for cp in self.cross_l:
            cp.finalize()

    def sample(self):
        # First, sample the coverpoints
        for cp in self.coverpoint_l:
            cp.sample()
            
        for cr in self.cross_l:
            cr.sample()

        if self.type_cg is not None:
            # Propagate cached values to the type
            for i in range(len(self.cross_l)):
                self.type_cg.cross_l[i].iff_val_cache = self.cross_l[i].iff_val_cache
                
            for i in range(len(self.coverpoint_l)):
                self.type_cg.coverpoint_l[i].target_val_cache = self.coverpoint_l[i].target_val_cache
                self.type_cg.coverpoint_l[i].iff_val_cache = self.coverpoint_l[i].iff_val_cache

            # Now, sample the type
            self.type_cg.sample()
            
    def add_coverpoint(self, cp):
        cp.parent = self
        if isinstance(cp, CoverpointModel):
            self.coverpoint_l.append(cp)
        elif isinstance(cp, CoverpointCrossModel):
            self.cross_l.append(cp)
        else:
            raise Exception("Unsupported model type %s" % (str(type(cp))))
        
        return cp
        
    def get_coverage(self):
        if not self.coverage_calc_valid:
            self.coverage = 0.0
            for cp in self.coverpoint_l:
                self.coverage += cp.get_coverage()
            for cp in self.cross_l:
                self.coverage += cp.get_coverage()
            
            if (len(self.coverpoint_l)+len(self.cross_l)) == 0:
                self.coverage = 100.0 # vacuously covered
            else:
                self.coverage /= (len(self.coverpoint_l) + len(self.cross_l))
                self.coverage = round(self.coverage, 4)
            self.coverage_calc_valid = True
            
        return self.coverage
        
    def coverage_ev(self, cp, bin_idx):
        self.coverage_calc_valid = False
    
    def get_inst_coverage(self):
        return 0.0
            
    def accept(self, v):
        v.visit_covergroup(self)
            
    def dump(self, ind=""):
        # Disabled functionality
        pass
#         print(ind + "Covergroup " + self.name)
#         for cp in self.coverpoint_l:
#             cp.dump(ind + "    ")
#         for cr in self.cross_l:
#             cr.dump(ind + "    ")

    def equals(self, oth : 'CovergroupModel')->bool:
        eq = True
        
        if len(self.coverpoint_l) == len(oth.coverpoint_l):
            for i in range(len(self.coverpoint_l)):
                eq &= self.coverpoint_l[i].equals(oth.coverpoint_l[i])
        else:
            eq = False                
            
        if len(self.cross_l) == len(oth.cross_l):
            for i in range(len(self.cross_l)):
                eq &= self.cross_l[i].equals(oth.cross_l[i])
        else:
            eq = False
            
        return eq
    
    def clone(self)->'CovergroupModel':
        ret = CovergroupModel(self.name)
        
        ret.srcinfo_decl = None if self.srcinfo_decl is None else self.srcinfo_decl.clone()
        ret.srcinfo_inst = None if self.srcinfo_inst is None else self.srcinfo_inst.clone()
        
        ret.du_name = self.du_name
        ret.instname = self.instname

        coverpoint_m = {}        
        for cp in self.coverpoint_l:
            cp_c = cp.clone()
            coverpoint_m[cp] = cp_c
            ret.add_coverpoint(cp_c)
        
        for cr in self.cross_l:
            ret.add_coverpoint(cr.clone(coverpoint_m))
            
        return ret
        