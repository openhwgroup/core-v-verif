
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
from ucis.statement_id import StatementId
from ucis.instance_coverage import InstanceCoverage

class MemInstanceCoverage(InstanceCoverage):
    
    def __init__(self, 
                 name : str,
                 key : str,
                 stmt_id : StatementId):
        self.name = name
        self.key = key
        self.stmt_id = stmt_id
        self.instanceId = None # optional
        self.alias = None # optional
        self.moduleName = None # optional
        self.parentInstanceId = -1 # optional
        self.design_parameter_l = []
        self.toggle_coverage_l = []
        self.block_coverage_l = []
        self.condition_coverage_l = []
        self.branch_coverage_l = []
        self.fsm_coverage_l = []
        self.assertion_coverage_l = []
        self.covergroup_coverage_l = []
        self.user_attr_l = []
        pass

    def getId(self)->StatementId:
        return self.stmt_id
    
    def getName(self)->str:
        return self.name
    
    def getKey(self)->str:
        return self.key