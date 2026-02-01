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


# Created on Jan 1, 2020
#
# @author: ballance

from vsc.model.constraint_scope_model import ConstraintScopeModel

class ConstraintBlockModel(ConstraintScopeModel):
    """Information about a top-level constraint block described by the user"""
    
    def __init__(self, name, constraints = None):
        super().__init__()
        self.name = name
        self.enabled = True
        self.is_dynamic = False
        
        if constraints is not None:
            for c in constraints:
                self.constraint_l.append(c)

    def set_constraint_enabled(self, en):
        self.enabled = en
        
    def accept(self, v):
        v.visit_constraint_block(self)
        
    def __str__(self):
        ret = "ConstraintBlock: "
        
        for c in self.constraint_l:
            ret += str(c) + "; "
            
        return ret
    
    def clone(self, deep=False)->'ConstraintModel':
        ret = ConstraintBlockModel(self.name)
        ret.enabled = self.enabled
        ret.is_dynamic = self.is_dynamic
        
        if deep:
            for c in self.constraint_l:
                ret.constraint_l.append(c.clone(deep))
        