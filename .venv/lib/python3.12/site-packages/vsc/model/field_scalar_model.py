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

# Created on Jul 24, 2019
#
# @author: ballance


from vsc.model.field_model import FieldModel
from vsc.model.rand_gen_data import RandGenData
from vsc.model.value import Value
from vsc.model.value_scalar import ValueScalar


class FieldScalarModel(FieldModel):
    
    def __init__(self, 
        name,
        width,
        is_signed,
        is_rand,
        rand_if=None): 
        super().__init__(name)
        self.width = width
        self.mask = (1 << width)-1
        self.is_signed = is_signed
        self.is_declared_rand = is_rand
        self.is_used_rand = is_rand
        self.rand_mode = is_rand
        self.rand_if = rand_if
        self.var = None
        self.val = ValueScalar(0)
        
    def set_used_rand(self, is_rand, level=0):
        # Field is considered rand when
        # - It is a root field, on which 'randomize' is called
        # - It is declared as random, and 'rand_mode' is true
        self.is_used_rand = (is_rand and 
                             ((self.is_declared_rand and self.rand_mode) or level==0))
        
    def dispose(self):
        self.var = None
        
    def accept(self, v):
        v.visit_scalar_field(self)

    def build(self, btor):
        if self.var is None:
            if self.is_used_rand:
                sort = btor.BitVecSort(self.width)
                self.var = btor.Var(sort)
            else:
                self.var = btor.Const(self.val.v, self.width)
        return self.var
    
    def get_full_name(self):
        ret = self.name
        p = self.parent
        
        while p is not None:
            if p.name is not None:
                ret = p.name + "." + ret
            p = p.parent

        return ret
        
        
    def __str__(self):
        return "FieldScalarModel(" + self.get_full_name() + ")"

    def get_constraints(self, constraint_l):
        pass

    def pre_randomize(self):
        if self.rand_if is not None:
            self.rand_if.do_pre_randomize()
    
    def set_val(self, val : Value):
        self.val.v = int(val)
        
    def get_val(self):
        return self.val
    
    def post_randomize(self):
        if self.var is not None:
            # Convert to a Python base-10 integer (unsigned)
            val = int(self.var.assignment, 2)
            
            if self.is_signed and (val&(1 << self.width-1)) != 0:
                # The value is actually signed, and must be
                # converted
                val = -((~val&self.mask)+1)
            
            self.set_val(val)
            
        if self.rand_if is not None:
            self.rand_if.do_post_randomize()
