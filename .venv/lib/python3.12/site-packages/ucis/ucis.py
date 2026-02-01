
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
Created on Dec 22, 2019

@author: ballance
'''

from ucis.history_node_kind import HistoryNodeKind
from typing import List, Iterator
from ucis.scope_type_t import ScopeTypeT
from ucis.unimpl_error import UnimplError
from ucis.scope import Scope
from ucis.history_node import HistoryNode
from ucis.source_file import SourceFile
from ucis.instance_coverage import InstanceCoverage
from ucis.statement_id import StatementId
from ucis.int_property import IntProperty
from ucis.file_handle import FileHandle

class UCIS(Scope):
    
    def __init__(self):
        pass
    
    def getIntProperty(
            self, 
            coverindex : int,
            property : IntProperty
            )->int:
        if property == IntProperty.IS_MODIFIED:
            return 1 if self.isModified() else 0
        elif property == IntProperty.MODIFIED_SINCE_SIM:
            return 1 if self.modifiedSinceSim() else 0
        elif property == IntProperty.NUM_TESTS:
            return self.getNumTests()
        else:
            return super().getIntProperty(coverindex, property)
    
    def setIntProperty(
            self,
            coverindex : int,
            property : IntProperty,
            value : int):
        super().setIntProperty(coverindex, property, value)
        
    def isModified(self):
        raise UnimplError()
    
    def modifiedSinceSim(self):
        raise UnimplError()
    
    def getNumTests(self):
        raise UnimplError()
    
    def getAPIVersion(self) -> str:
        raise UnimplError()
    
    def getWrittenBy(self)->str:
        raise UnimplError()
    
    def setWrittenBy(self, by : str):
        raise UnimplError()

    def getWrittenTime(self)->int:
        raise UnimplError()
    
    def setWrittenTime(self, time : int):
        raise UnimplError()
    
    def getDBVersion(self):
        raise UnimplError()
    
    def getPathSeparator(self):
        raise UnimplError()

    def setPathSeparator(self):
        raise UnimplError()
    
    def createFileHandle(self, filename, workdir)->FileHandle:
        raise UnimplError()
    
    def createHistoryNode(self, parent, logicalname, physicalname, kind):
        raise UnimplError()
    
    def historyNodes(self, kind : HistoryNodeKind) -> Iterator[HistoryNode]:
        raise UnimplError()
    
    def getHistoryNodes(self, kind : HistoryNodeKind) -> List[HistoryNode]:
        return list(self.historyNodes(kind))
    
    def getSourceFiles(self) -> [SourceFile]:
        raise UnimplError()
    
    def getCoverInstances(self) -> [InstanceCoverage]:
        raise UnimplError()
    
    def write(self, file, scope=None, recurse=True, covertype=-1):
        raise UnimplError()

    def close(self):
        """Close the database and commit changes to backing storage"""
        raise UnimplError()
