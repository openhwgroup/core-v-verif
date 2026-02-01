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


class FieldCompositeModel(FieldModel):
    
    def __init__(self, name, is_rand=False, rand_if=None):
        if name is None:
            name = "root"
        super().__init__(name)
        # Captures whether this field was declared rand
        self.is_declared_rand = is_rand
        # Captures whether this field is being used as rand
        self.is_used_rand = is_rand
        self.rand_mode = is_rand
        self.rand_if = rand_if
        self.field_l = []
        self.field_id_m = {}
        self.constraint_model_l = []
        self.constraint_dynamic_model_l = []
        self.constraint_dynamic_m = {}
        self.exec_l = []
        self.function_l = []
        self.constraint_l = []

    def finalize(self):
        pass
    
    @property
    def is_declared_rand(self):
        return self.__is_declared_rand
    
    @is_declared_rand.setter
    def is_declared_rand(self, v):
        self.__is_declared_rand = bool(v)
        self.rand_mode = bool(v)
    
    def set_used_rand(self, is_rand, level=0):
        self.is_used_rand = (is_rand and 
                             ((self.is_declared_rand and self.rand_mode) or level==0))

        for f in self.field_l:
            f.set_used_rand(self.is_used_rand, level+1)
            
    def build(self, builder):
        # First, build the fields
        for f in self.field_l:
            f.build(builder)

        # Next, build out the constraints
        for c in self.constraint_model_l:
            c.build(builder)

#        for f in self.field_l:
#            if isinstance(f, FieldCompositeModel):
#                f.build

    def add_field(self, f)->FieldModel:
        f.parent = self
        f.idx    = len(self.field_l)
        self.field_id_m[f.name] = f.idx
        self.field_l.append(f)
        return f
        
    def get_field(self, idx):
        return self.field_l[idx]
    
    def set_field(self, idx, f):
        f.parent = self
        f.idx = idx
        self.field_l[idx] = f
        
    def find_field(self, name):
        for f in self.field_l:
            if f.name == name:
                return f
        return None
        
    def add_constraint(self, c):
        c.parent = self
        self.constraint_model_l.append(c)
        
    def get_constraint(self, name):
        for c in self.constraint_model_l:
            if c.name == name:
                return c
            
        return None
        
    def add_dynamic_constraint(self, c):
        c.parent = self
        self.constraint_dynamic_m[c.name] = len(self.constraint_dynamic_model_l)
        self.constraint_dynamic_model_l.append(c)
        
    def get_constraints(self, constraint_l):
        for f in self.field_l:
            f.get_constraints(constraint_l)
            
        for c in self.constraint_model_l:
            constraint_l.append(c)
            
    def get_fields(self, field_l):
        for f in self.field_l:
            if isinstance(f, FieldCompositeModel):
                f.get_fields(field_l)
            else:
                field_l.append(f)

    def pre_randomize(self):
        """Called during the randomization process to propagate `pre_randomize` event"""
        
        # Perform a phase callback if available. Note,
        # only trigger pre_randomize callbacks on composite
        # fields that are actually being used as random
        if self.is_used_rand and self.rand_if is not None:
            self.rand_if.do_pre_randomize()
            
        for f in self.field_l:
            f.pre_randomize()
    
    def post_randomize(self):
        """Called during the randomization process to propagate `post_randomize` event"""
        
        # Perform a phase callback if available
        if self.is_used_rand and self.rand_if is not None:
            self.rand_if.do_post_randomize()
            
        for f in self.field_l:
            f.post_randomize()

    def accept(self, v):
        v.visit_composite_field(self)
        
    def dispose(self):
        for f in self.field_l:
            f.dispose()
        
            
