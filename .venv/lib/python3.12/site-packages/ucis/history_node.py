from ucis.test_status_t import TestStatusT
from ucis.history_node_kind import HistoryNodeKind

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
from ucis.unimpl_error import UnimplError
from ucis.test_data import TestData
from ucis.obj import Obj
from ucis.int_property import IntProperty

class HistoryNode(Obj):
    
    def __init__(self):
        super().__init__()
    
    def setTestData(self, testdata : TestData):
        self.setTestStatus(testdata.teststatus)
        self.setToolCategory(testdata.toolcategory)
        self.setDate(testdata.date)
        self.setSimTime(testdata.simtime)
        self.setTimeUnit(testdata.timeunit)
        self.setRunCwd(testdata.runcwd)
        self.setCpuTime(testdata.cputime)
        self.setSeed(testdata.seed)
        self.setCmd(testdata.cmd)
        self.setArgs(testdata.args)
        self.setCompulsory(testdata.compulsory)
        self.setUserName(testdata.user)
        self.setCost(testdata.cost)
   
    def getUserAttr(self):
        raise UnimplError()
    
    def getParent(self):
        raise UnimplError()
    
    def getLogicalName(self) -> str:
        raise UnimplError()
    
    def setLogicalName(self, name : str):
        raise UnimplError()
    
    def getPhysicalName(self) -> str:
        raise UnimplError()
    
    def setPhysicalName(self, name : str):
        raise UnimplError()
    
    def getKind(self) -> HistoryNodeKind:
        raise UnimplError()
    
    def getTestStatus(self) -> TestStatusT:
        raise UnimplError()
    
    def setTestStatus(self, status : TestStatusT):
        raise UnimplError()
    
    def getSimTime(self) -> float:
        raise UnimplError()
    
    def setSimTime(self, time : float):
        raise UnimplError()
    
    def getTimeUnit(self) -> str:
        raise UnimplError()
    
    def setTimeUnit(self, unit : str):
        raise UnimplError()
    
    def getRunCwd(self) -> str:
        raise UnimplError()
    
    def setRunCwd(self, cwd : str):
        raise UnimplError()
    
    def getCpuTime(self) -> float:
        raise UnimplError()
    
    def setCpuTime(self, time : float):
        raise UnimplError()
    
    def getSeed(self) -> str:
        raise UnimplError()
    
    def setSeed(self, seed : str):
        raise UnimplError()
    
    def getCmd(self) -> str:
        raise UnimplError()
    
    def setCmd(self, cmd : str):
        raise UnimplError()
    
    def getArgs(self) -> [str]:
        raise UnimplError()
    
    def setArgs(self, args : [str]):
        raise UnimplError()
    
    def getCompulsory(self) -> [str]:
        raise UnimplError()
    
    def setCompulsory(self, compulsory : [str]):
        raise UnimplError()
    
    def getDate(self)->int:
        raise UnimplError()
    
    def setDate(self, date : int):
        raise UnimplError()
    
    def getUserName(self) -> str:
        raise UnimplError()
    
    def setUserName(self, user : str):
        raise UnimplError()
    
    def getCost(self) -> int:
        raise UnimplError()
    
    def setCost(self, cost : int):
        raise UnimplError()
    
    def getToolCategory(self) -> str:
        raise UnimplError()
    
    def setToolCategory(self, category : str):
        raise UnimplError()
    
    def getUCISVersion(self) -> str:
        raise UnimplError()
    
    def getVendorId(self) -> str:
        raise UnimplError()
    
    def setVendorId(self, tool : str):
        raise UnimplError()
    
    def getVendorTool(self) -> str:
        raise UnimplError()
    
    def setVendorTool(self, tool : str):
        raise UnimplError()
    
    def getVendorToolVersion(self) -> str:
        raise UnimplError()
    
    def setVendorToolVersion(self, version : str):
        raise UnimplError()
    
    def getSameTests(self) -> int:
        raise UnimplError()
    
    def setSameTests(self, test_l : int):
        raise UnimplError()
    
    def getComment(self):
        raise UnimplError()
    
    def setComment(self, comment):
        raise UnimplError()
        
        
        
    
