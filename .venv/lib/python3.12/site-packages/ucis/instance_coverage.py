
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
Created on Jan 5, 2020

@author: ballance
'''
from ucis.name_value import NameValue
from ucis.unimpl_error import UnimplError
from ucis.statement_id import StatementId

class InstanceCoverage():
    
    def __init__(self):
        pass
    
    
    def getDesignParameters(self) -> [NameValue]:
        raise UnimplError()
    
    def addDesignParameter(self, p : NameValue):
        raise UnimplError()
    
    def getId(self) -> StatementId:
        raise UnimplError()
    
    def getName(self) -> str:
        raise UnimplError()
    
    def getKey(self) -> str:
        raise UnimplError()
    
    