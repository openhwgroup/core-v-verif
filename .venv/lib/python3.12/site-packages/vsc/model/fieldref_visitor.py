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


# Created on Aug 10, 2019
#
# @author: ballance

from vsc.model.model_visitor import ModelVisitor

class FieldrefVisitor(ModelVisitor):
    
    def __init__(self, ref_s, unref_s):
        self.ref_s = ref_s
        self.unref_s = unref_s
        self.phase = 0
        
    @staticmethod
    def find(obj, ref_s, unref_s):
        v = FieldrefVisitor(ref_s, unref_s)
        v.visit(obj)
        
    def visit(self, r):
        if self.ref_s is not None:
            self.ref_s.clear()
        if self.unref_s is not None:
            self.unref_s.clear()
        self.phase = 0
        r.accept(self)
        self.phase = 1
        r.accept(self)
        
    def visit_inline_constraint(self, c):
        self.phase = 0
        c.accept(self)
        
    def visit_scalar_field(self, f):
            
        if self.phase == 1 and self.unref_s is not None:
            if self.ref_s is not None and f not in self.ref_s:
                self.unref_s.add(f)
                
    def visit_expr_bin(self, e):
        super().visit_expr_bin(e)
    
    def visit_expr_fieldref(self, e):
        if self.phase == 0 and self.ref_s is not None:
            self.ref_s.add(e.fm)

