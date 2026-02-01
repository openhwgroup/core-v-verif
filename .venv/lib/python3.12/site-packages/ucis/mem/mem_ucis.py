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
from typing import Iterator
from ucis.mem.mem_history_node_iterator import MemHistoryNodeIterator
from ucis.mem.mem_file_handle import MemFileHandle
'''
Created on Jan 5, 2020

@author: ballance
'''

from datetime import datetime
import getpass
from ucis.flags_t import FlagsT
from ..history_node import HistoryNode
from ..history_node_kind import HistoryNodeKind
from ..instance_coverage import InstanceCoverage
from ..mem.mem_du_scope import MemDUScope
from ..mem.mem_history_node import MemHistoryNode
from ..mem.mem_instance_coverage import MemInstanceCoverage
from ..mem.mem_instance_scope import MemInstanceScope
from ..mem.mem_scope import MemScope
from ..mem.mem_source_file import MemSourceFile
from ..scope_type_t import ScopeTypeT
from ..source_file import SourceFile
from ucis.source_info import SourceInfo
from ucis.source_t import SourceT
from ucis.statement_id import StatementId
from ucis.ucis import UCIS
from ucis.unimpl_error import UnimplError


class MemUCIS(MemScope,UCIS):
    
    def __init__(self):
        MemScope.__init__(
            self,
            None,
            "",
            None,
            1,
            SourceT.NONE,
            ScopeTypeT.RESERVEDSCOPE,
            0)
        UCIS.__init__(self)
        self.ucis_version = "1.0"
        self.writtenBy = getpass.getuser()
        self.writtenTime = int(datetime.timestamp(datetime.now()))
        self.file_handle_m : Dict[str,MemFileHandle] = {}
        self.m_history_node_l = []
        self.m_instance_coverage_l = []
        
        self.m_du_scope_l = []
        self.m_inst_scope_l = []
    
    def getAPIVersion(self)->str:
        return "1.0"
    
    def getWrittenBy(self)->str:
        return self.writtenBy
    
    def setWrittenBy(self, by):
        self.writtenBy = by
    
    def getWrittenTime(self)->int:
        return self.writtenTime
    
    def setWrittenTime(self, time : int):
        self.writtenTime = time
    
    def createFileHandle(self, filename, workdir):
        if filename not in self.file_handle_m.keys():
            self.file_handle_m[filename] = MemFileHandle(filename)
        return self.file_handle_m[filename]
    

    
    def createHistoryNode(self, parent, logicalname, physicalname=None, kind=None):
        ret = MemHistoryNode(parent, logicalname, physicalname, kind)
        self.m_history_node_l.append(ret)
        return ret

    def createCoverInstance(self, name, stmt_id : StatementId):
        ret = MemInstanceCoverage(name, str(len(self.m_instance_coverage_l)), stmt_id)
        self.m_instance_coverage_l.append(ret)
        return ret
        
    def historyNodes(self, kind:HistoryNodeKind)->Iterator[HistoryNode]:
        return MemHistoryNodeIterator(self.m_history_node_l, kind)
    
    def getCoverInstances(self)->[InstanceCoverage]:
        return self.m_instance_coverage_l
    
    def close(self):
        # NOP
        pass

    
    