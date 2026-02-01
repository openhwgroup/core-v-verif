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
from ucis.int_property import IntProperty
from ucis.lib.lib_cover_index import LibCoverIndex
from ucis.lib.lib_scope_iterator import LibScopeIterator
from typing import Iterator
'''
Created on Jan 11, 2020

@author: ballance
'''

from _ctypes import byref, pointer
from ucis.scope import Scope
from ucis.unimpl_error import UnimplError
from ucis.cover_data import CoverData
from ucis.flags_t import FlagsT
from ucis.lib.lib_cover_data import LibCoverData
from ucis.lib.lib_obj import LibObj
from ucis.lib.lib_source_info import _LibSourceInfo, LibSourceInfo
from ucis.lib.libucis import get_lib
from ucis.scope_type_t import ScopeTypeT
from ucis.source_info import SourceInfo
from ucis.source_t import SourceT
from ucis.toggle_dir_t import ToggleDirT
from ucis.toggle_metric_t import ToggleMetricT
from ucis.toggle_type_t import ToggleTypeT


class LibScope(LibObj, Scope):
    
    def __init__(self, db, obj):
        LibObj.__init__(self, db, obj)
        Scope.__init__(self)
        logging.debug("LibScope::init - db=" + str(self.db) + " " + str(self.obj))
        
    def getGoal(self)->int:
        return self.getIntProperty(-1, IntProperty.SCOPE_GOAL)
    
    def setGoal(self,goal)->int:
        self.setIntProperty(-1, IntProperty.SCOPE_GOAL, goal)
        
#     def getWeight(self):
#         return self.getIntProperty(-1, IntProperty.SCOPE_WEIGHT)
#     
#     def setWeight(self, w):
#         self.setIntProperty(-1, IntProperty.SCOPE_WEIGHT, w)
        
    def createScope(self, 
        name:str, 
        srcinfo:SourceInfo, 
        weight:int, 
        source, 
        type, 
        flags):
        srcinfo_p = None if srcinfo is None else byref(_LibSourceInfo.ctor(srcinfo))
        logging.debug("createScope: db=" + str(self.db) + " obj=" + str(self.obj) + 
              " name=" + str(name) + " srcinfo_p=" + str(srcinfo_p) +
              " weight=" + str(weight) + "source=" + hex(source) + " type=" + hex(type) + " flags=" + hex(flags));
        sh = get_lib().ucis_CreateScope(
            self.db,
            self.obj,
            None if name is None else str.encode(name),
            srcinfo_p,
            weight,
            source,
            type,
            flags)
        
        if sh is None:
            logging.error("createScope failed: parent=" + str(self.obj))
            raise Exception("Failed to create scope")
        
        return LibScope(self.db, sh)
    
    def createInstance(self,
                    name : str,
                    fileinfo : SourceInfo,
                    weight : int,
                    source : SourceT,
                    type : ScopeTypeT,
                    du_scope : Scope,
                    flags : FlagsT):
        fileinfo_p = None if fileinfo is None else byref(_LibSourceInfo.ctor(fileinfo))
        sh = get_lib().ucis_CreateInstance(
            self.db,
            self.obj,
            str.encode(name),
            fileinfo_p,
            weight,
            source,
            type,
            du_scope.obj,
            flags)
        
        if sh is None:
            logging.error("ucis_CreateInstance failed: du=" + str(du_scope) + " du.obj=" + str(du_scope.obj))
            raise Exception("ucis_CreateInstance failed")
        
        return LibScope(self.db, sh)
    
    def createCovergroup(self, 
        name:str, 
        srcinfo:SourceInfo, 
        weight:int, 
        source) -> 'Covergroup':
        from ucis.lib.lib_covergroup import LibCovergroup
        
        srcinfo_p = None if srcinfo is None else pointer(_LibSourceInfo.ctor(srcinfo))
        cg_obj = get_lib().ucis_CreateScope(
            self.db,
            self.obj,
            str.encode(name),
            srcinfo_p,
            weight,
            source,
            ScopeTypeT.COVERGROUP,
            0)
        
        return LibCovergroup(self.db, cg_obj)
    
    def createToggle(self,
                    name : str,
                    canonical_name : str,
                    flags : FlagsT,
                    toggle_metric : ToggleMetricT,
                    toggle_type : ToggleTypeT,
                    toggle_dir : ToggleDirT) -> 'Scope':
        th = get_lib().ucis_CreateToggle(
            self.db,
            self.obj,
            str.encode(name),
            None if canonical_name is None else str.encode(canonical_name),
            flags,
            toggle_metric,
            toggle_type,
            toggle_dir)
        return LibScope(self.db, th)
    
    def createNextCover(self,
                        name : str,
                        data : CoverData,
                        sourceinfo : SourceInfo) -> int:
        sourceinfo_p = None if sourceinfo is None else byref(_LibSourceInfo.ctor(sourceinfo))
        data_p = byref(LibCoverData.ctor(data))
        
        index =  get_lib().ucis_CreateNextCover(
            self.db,
            self.obj,
            str.encode(name),
            data_p,
            sourceinfo_p)
        
        return LibCoverIndex(self.db, self.obj, index)
    
    def getSourceInfo(self)->SourceInfo:
        libsrcinfo = _LibSourceInfo()
        sourceinfo_p = byref(libsrcinfo)
        
        get_lib().ucis_GetScopeSourceInfo(self.db, self.obj, sourceinfo_p)
        
        return LibSourceInfo.ctor(self.db, libsrcinfo)
    
    def scopes(self, mask:ScopeTypeT)->Iterator['Scope']:
        return LibScopeIterator(self.db, self.obj, mask)
        