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


# Created on Jul 28, 2019
#
#@author: ballance

from vsc.model.constraint_scope_model import ConstraintScopeModel
from vsc.model.expr_model import ExprModel


class ConstraintImpliesModel(ConstraintScopeModel):
    
    def __init__(self, cond, constraints=None):
        super().__init__(constraints)
        self.cond = cond
        
    def build(self, btor):
        cond = ExprModel.toBool(btor, self.cond.build(btor))
        body = super().build(btor)
        
        return btor.Implies(cond, body)
    
    def get_nodes(self, node_l):
        node_l.append(self.node)
        
    def accept(self, visitor):
        visitor.visit_constraint_implies(self)
        
    def clone(self, deep=False)->'ConstraintModel':
        ret = ConstraintImpliesModel(self.cond)
        
        if deep:
            for c in self.constraint_l:
                ret.constraint_l.append(c.clone(deep))
        
        return ret
        