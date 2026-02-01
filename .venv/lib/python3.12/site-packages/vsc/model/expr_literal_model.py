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

from vsc.model.expr_model import ExprModel
from vsc.model.value import Value
from vsc.model.value_scalar import ValueScalar


class ExprLiteralModel(ExprModel):
    
    def __init__(self, val, is_signed, width):
        super().__init__()
        self._val = ValueScalar(val)
        self.signed = is_signed
        self._width = width
        
        if width < 1:
            raise Exception("Error: literal with a width of " + str(width))
        
    def build(self, btor, ctx_width=-1):
        if self._width > ctx_width:
            ctx_width = self._width
        return btor.Const(int(self.val()), ctx_width)
    
    def is_signed(self):
        return self.signed
    
    def width(self):
        return self._width
    
    def accept(self, visitor):
        visitor.visit_expr_literal(self)
        
    def val(self):
        return self._val
        
    def __str__(self):
        return "Literal: " + str(self._val)
        
