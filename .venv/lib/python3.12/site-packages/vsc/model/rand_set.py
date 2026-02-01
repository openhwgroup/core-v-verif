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


# Created on Jan 22, 2020
#
# @author: ballance

from builtins import set
from typing import Set, List

from vsc.model.constraint_model import ConstraintModel
from vsc.model.field_model import FieldModel
from vsc.model.constraint_soft_model import ConstraintSoftModel
from vsc.visitors.model_pretty_printer import ModelPrettyPrinter


class RandSet(object):
    """Contains information about one set of related fields and constraints"""
    
    def __init__(self, order=-1):
        self.order = order
        self.field_s : Set[FieldModel] = set()
        self.field_rand_l = []
        self.all_field_l = []
        
        self.constraint_s :Set[ConstraintModel] = set()
        self.constraint_l : List[ConstraintModel] = []
        self.soft_constraint_s : Set[ConstraintModel] = set()
        self.soft_constraint_l : List[ConstraintModel] = []
        self.soft_priority = 0
        self.dist_field_m = {}

        # List of fields in each ordered set
        # Only non-none if order constraints impact this randset
        self.rand_order_l = None
        
    def build(self, btor, constraint_l):
        for f in self.all_field_l:
            f.build(btor)
        for c in self.constraint_l:
            c.build(btor)
    
    def dispose(self):
        for f in self.all_field_l:
            f.dispose()
        for c in self.constraint_l:
            c.dispose()
        
    def add_field(self, f):
        if f not in self.field_s:
            self.field_s.add(f)
            if f.is_used_rand:
                self.field_rand_l.append(f)
            self.all_field_l.append(f)
            
    def fields(self):
        return self.all_field_l
    
    def rand_fields(self):
        return self.field_rand_l
    
    def all_fields(self)->List[FieldModel]:
        return self.all_field_l
        
    def add_constraint(self, c):
        if isinstance(c, ConstraintSoftModel):
            if c not in self.soft_constraint_s:
                self.soft_constraint_s.add(c)
                self.soft_constraint_l.append(c)
        else:
            if c not in self.constraint_s:
                self.constraint_s.add(c)
                self.constraint_l.append(c)
        
    def constraints(self) ->List[ConstraintModel]:
        return self.constraint_l
    
    def soft_constraints(self) -> List[ConstraintSoftModel]:
        return self.soft_constraint_l

    
