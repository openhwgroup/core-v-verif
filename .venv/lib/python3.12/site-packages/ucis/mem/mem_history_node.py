from ucis.test_status_t import TestStatusT

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
from ucis.history_node import HistoryNode
from datetime import datetime
from ucis.test_data import TestData
from ucis.int_property import IntProperty

class MemHistoryNode(HistoryNode):
    
    def __init__(self, 
                 parent,
                 logicalname,
                 physicalname,
                 kind):
        
        self.m_parent = parent
        self.m_logicalname = logicalname
        self.m_physicalname = physicalname
        self.m_kind = kind
        self.m_test_status = TestStatusT.OK
        self.m_sim_time = -1.0
        self.m_time_unit = None
        self.m_run_cwd = None
        self.m_cpu_time = -1.0
        self.m_seed = None
        self.m_cmd = None
        self.m_args = None
        self.m_compulsory = None
        self.m_date = int(datetime.timestamp(datetime.now()))
        self.m_user_name = None
        self.m_cost = -1
        self.m_tool_category = "unknown"
        self.m_ucis_version = "1.0"
        self.m_vendor_id = "unknown"
        self.m_vendor_tool = "unknown"
        self.m_vendor_tool_version = "unknown"
        self.m_same_tests =  -1
        self.m_comment = None
        
    def getParent(self):
        return self.m_parent
    
    def getIntProperty(
        self, 
        coverindex:int, 
        property:IntProperty)-> int:
        if property == IntProperty.TEST_STATUS:
            return 1 if self.m_test_status else 0
        else:
            return super().getIntProperty(coverindex, property)
        
    def setIntProperty(
        self, 
        coverindex:int, 
        property:IntProperty, 
        value:int):
        if property == IntProperty.TEST_STATUS:
            self.m_test_status = (value==1)
        else:
            super().setIntProperty(coverindex, property, value)
    
    def getLogicalName(self)->str:
        return self.m_logicalname
    
    def getPhysicalName(self)->str:
        return self.m_physicalname
    
    def getKind(self)->str:
        return self.m_kind
    
    def getTestStatus(self) -> TestStatusT:
        return self.m_test_status
    
    def setTestStatus(self, status : TestStatusT):
        self.m_test_status = status
    
    def getSimTime(self)->float:
        return self.m_sim_time
    
    def setSimTime(self, time:float):
        self.m_sim_time = time
        
    def getTimeUnit(self) -> str:
        return self.m_time_unit
    
    def setTimeUnit(self, unit : str):
        self.m_time_unit = unit
    
    def getRunCwd(self) -> str:
        return self.m_run_cwd
    
    def setRunCwd(self, cwd : str):
        self.m_run_cwd = cwd
    
    def getCpuTime(self) -> float:
        return self.m_cpu_time
    
    def setCpuTime(self, time : float):
        self.m_cpu_time = time
    
    def getSeed(self) -> str:
        return self.m_seed
    
    def setSeed(self, seed : str):
        self.m_seed = seed
    
    def getCmd(self) -> str:
        return self.m_cmd
    
    def setCmd(self, cmd : str):
        self.m_cmd = cmd
    
    def getArgs(self) -> [str]:
        return self.m_args
    
    def setArgs(self, args : [str]):
        self.m_args = args
    
    def getCompulsory(self) -> [str]:
        return self.m_compulsory
    
    def setCompulsory(self, compulsory : [str]):
        self.m_compulsory = compulsory
    
    def getDate(self):
        return self.m_date
    
    def setDate(self, date):
        self.m_date = date
    
    def getUserName(self) -> str:
        return self.m_user_name
    
    def setUserName(self, user : str):
        self.m_user_name = user
    
    def getCost(self) -> int:
        return self.m_cost
    
    def setCost(self, cost : int):
        self.m_cost = cost
    
    def getToolCategory(self) -> str:
        return self.m_tool_category
    
    def setToolCategory(self, category : str):
        self.m_tool_category = category
    
    def getUCISVersion(self) -> str:
        return self.m_ucis_version
    
    def getVendorId(self) -> str:
        return self.m_vendor_id
    
    def setVendorId(self, vendor_id : str):
        self.m_vendor_id = vendor_id
    
    def getVendorTool(self) -> str:
        return self.m_vendor_tool
    
    def setVendorTool(self, tool : str):
        self.m_vendor_tool = tool
        
    def getVendorToolVersion(self) -> str:
        return self.m_vendor_tool_version
    
    def setVendorToolVersion(self, version : str):
        self.m_vendor_tool_version = version
    
    def getSameTests(self) -> int:
        return self.m_same_tests
    
    def setSameTests(self, test_l : int):
        self.m_same_tests = test_l
    
    def getComment(self):
        return self.m_comment
    
    def setComment(self, comment):
        self.m_comment = comment
    
    