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


# Created on Jul 26, 2019
#
# @author: ballance


from vsc.model.expr_model import ExprModel

class ExprFieldRefModel(ExprModel):
    
    def __init__(self, fm):
        super().__init__()
        self.fm = fm
        
        if fm is None:
            raise Exception("Field Model None specified")

    def build(self, btor, ctx_width=-1):
        if self.fm.var is None:
            raise Exception("Field " + str(self.fm) + " (" + self.fm.name + ") has not been built")
        return self.fm.var
        
    def is_signed(self):
        return self.fm.is_signed
    
    def width(self):
        return self.fm.width
    
    def accept(self, visitor):
        visitor.visit_expr_fieldref(self)
        
    def val(self):
        return self.fm.val
        
    def __str__(self):
        return "Field: " + self.fm.name