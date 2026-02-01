
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

'''
Created on Jan 8, 2020

@author: ballance
'''
from ucis.scope import Scope
from ucis.unimpl_error import UnimplError

class CoverType(Scope):
    
    def __init__(self):
        super().__init__()
        
    def setCoverGoal(self, goal : int):
        raise UnimplError()
    
    def getCoverGoal(self)->int:
        raise UnimplError()
    
    def setCoverLimit(self, limit : int):
        raise NotImplementedError()
    
    def getCoverLimit(self) -> int:
        raise NotImplementedError()
    
    def setCoverWeight(self, weight : int):
        raise NotImplementedError()
    
    def getCoverWeight(self) -> int:
        raise NotImplementedError()
    
        