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
import logging
from typing import List, Iterator
from ucis.str_property import StrProperty
'''
Created on Jan 10, 2020

@author: ballance
'''

from ucis.file_handle import FileHandle
from ucis.history_node import HistoryNode
from ucis.history_node_kind import HistoryNodeKind
from ucis.int_property import IntProperty
from ucis.lib.lib_file_handle import LibFileHandle
from ucis.lib.lib_history_node import LibHistoryNode
from ucis.lib.lib_scope import LibScope
from ucis.lib.libucis import _lib, get_ucis_library, get_lib
from ucis.ucis import UCIS


class LibUCIS(LibScope,UCIS):
    
    def __init__(self, file : str=None, db=None):
        if db is None:
            db = get_lib().ucis_Open(
                str.encode(file) if file is not None else None)
        
            if db is None:
                if file is not None:
                    raise Exception("Error: failed to open UCIS file \"" + file + "\"")
                else:
                    raise Exception("Error: failed to create UCIS DB")
        super().__init__(db, None)
        
    def isModified(self):
        return get_lib().ucis_GetIntProperty(self.db, -1, IntProperty.IS_MODIFIED) == 1
    
    def modifiedSinceSim(self):
        return get_lib().ucis_GetIntProperty(self.db, -1, IntProperty.MODIFIED_SINCE_SIM) == 1
        
    def getNumTests(self):
        return get_lib().ucis_GetIntProperty(self.db, -1, IntProperty.NUM_TESTS)
    
    def getAPIVersion(self)->str:
        # TODO
        return "1.0"
    
    def getWrittenBy(self)->str:
        return self.getStringProperty(-1, StrProperty.TEST_USERNAME)
    
    def createFileHandle(self, filename, workdir)->FileHandle:
        fh = get_lib().ucis_CreateFileHandle(
            self.db,
            str.encode(filename),
            None if workdir is None else str.encode(workdir))
        
        return LibFileHandle(self.db, fh)
        
    
    def createHistoryNode(self, parent, logicalname, physicalname, kind) -> 'HistoryNode':
        logging.debug("--> createHistoryNode")
        logging.debug("  db=" + str(self.db))
        logging.debug("  parent=" + str(parent))
        logging.debug("  logicalname=" + str(logicalname))
        logging.debug("  physicalname=" + str(physicalname))
        logging.debug("  kind=" + str(kind))
        
        hn = get_lib().ucis_CreateHistoryNode(
            self.db,
            parent,
            str.encode(logicalname),
            str.encode(physicalname),
            kind)
        logging.debug("hn=" + str(hn))
        logging.debug("<-- createHistoryNode")
        return LibHistoryNode(self.db, hn)
    
    def getHistoryNodes(self, kind:HistoryNodeKind)->List[HistoryNode]:
        
        UCIS.getHistoryNodes(self, kind)
        
    def historyNodes(self, kind:HistoryNodeKind)->Iterator[HistoryNode]:
        UCIS.historyNodes(self, kind)
        
    def write(self, file, scope=None, recurse=True, covertype=-1):
        logging.debug("file=" + file)
        ret = get_lib().ucis_Write(
            self.db, 
            str.encode(file),
            scope,
            1 if recurse else 0,
            covertype)
        logging.debug("ret=" + str(ret))
        
    def close(self):
        ret = get_lib().ucis_Close(self.db)
        logging.debug("close ret=" + str(ret))
