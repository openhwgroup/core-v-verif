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

# Created on Jul 27, 2019
#
# @author: ballance

from vsc.model.expr_indexed_field_ref_model import ExprIndexedFieldRefModel
from vsc.model.expr_fieldref_model import ExprFieldRefModel
from vsc.model.source_info import SourceInfo
from vsc.model.value import Value



class FieldModel(object):
    
    def __init__(self, name):
        self.parent       = None
        self.idx          = -1
        self.name         = name
        self.typename     = "<unknown>"
        self.srcinfo_decl = None
        self.srcinfo_inst = None
    
    def build(self, builder):
        raise Exception("FieldModel::build unimplemented for type " + str(type(self)))

    def pre_randomize(self):
        pass

    def post_randomize(self):
        pass
    
    def get_val(self) -> Value:
        raise NotImplementedError("FieldModel::get_val unimplemented for " + str(type(self)))
    
    def set_val(self, v : Value):
        raise NotImplementedError("FieldModel::set_val unimplemented for " + str(type(self)))
    
    @property
    def fullname(self):
        ret = self.name
        p = self.parent
        
        while p is not None:
            if p.name is not None:
                ret = p.name + "." + ret
            p = p.parent
            
        return ret
    
    def expr(self):
        """Returns a field-reference expression for this field"""
        return ExprFieldRefModel(self)
    
    def get_indexed_fieldref_expr(self):
        if self.parent is None:
            raise Exception("Field has no parent")
        else:
            idx_l = []
            p = self.parent
            s = self
            while p is not None:
                idx_l.insert(0, s.idx)
                s = p
                p = p.parent
            
            return ExprIndexedFieldRefModel(s, idx_l)
        