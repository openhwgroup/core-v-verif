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


class ExprModel(object):
    
    def __init__(self):
        self.srcinfo = None
        pass
    
    def build(self, btor, ctx_width=-1):
        raise Exception("Expression build() unimplemented for " + str(type(self)))
    
    def is_signed(self):
        raise Exception("is_signed unimplemented (" + str(type(self)) + ")")
    
    def width(self):
        raise Exception("width unimplemented (" + str(type(self)) + ")")
        
    def accept(self, v):
        raise Exception("" + str(self) + "::accept not implemented")

    def val(self):
        '''
        Return the value of this expression
        '''
        raise Exception("val unimplemented for " + str(type(self)))
    
    @staticmethod
    def toBool(btor, n):
        if n.width == 1:
            return n
        else:
            return btor.Ne(n, btor.Const(0, n.width))
        
    
