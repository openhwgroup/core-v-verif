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

from typing import Iterator, List
from ucis.int_property import IntProperty
from ucis.cover_data import CoverData
from ucis.cover_index import CoverIndex
from ucis.cover_type_t import CoverTypeT
from ucis.flags_t import FlagsT
from ucis.mem.mem_obj import MemObj
from ucis.mem.mem_scope_iterator import MemScopeIterator
from ucis.scope import Scope
from ucis.scope_type_t import ScopeTypeT
from ucis.source_info import SourceInfo
from ucis.source_t import SourceT
from ucis.toggle_dir_t import ToggleDirT
from ucis.toggle_metric_t import ToggleMetricT
from ucis.toggle_type_t import ToggleTypeT
from ucis.unimpl_error import UnimplError

from ucis.mem.mem_cover_index import MemCoverIndex
from ucis.mem.mem_cover_index_iterator import MemCoverIndexIterator


class MemScope(MemObj,Scope):
    
    def __init__(self,
                 parent : 'MemScope',
                 name : str,
                 srcinfo : SourceInfo,
                 weight : int,
                 source : SourceT,
                 type : ScopeTypeT,
                 flags : FlagsT):
        super().__init__()
        self.m_parent = parent
        self.m_name = name
        self.m_srcinfo = srcinfo if srcinfo is not None else SourceInfo(None, -1, -1)
        self.m_weight = weight
        self.m_source = source
        self.m_type = type
        self.m_flags = flags
        self.m_goal = -1
        self.m_source_type = 0
        self.m_is_under_du = 0
        self.m_children = []
        self.m_cover_items : List['CoverIndex'] = []
        
    def addChild(self, c):
        self.m_children.append(c)
        
    def getWeight(self):
        return self.m_weight
    
    def setWeight(self, w):
        self.m_weight = w
        
    def getGoal(self)->int:
        return self.m_goal
    
    def setGoal(self, goal):
        self.m_goal = goal
        
    def getScopeType(self)->ScopeTypeT:
        return self.m_type
    
    def getScopeName(self)->str:
        return self.m_name
        
    def getSourceInfo(self)->SourceInfo:
        return self.m_srcinfo
        
    def getIntProperty(
            self, 
            coverindex : int,
            property : IntProperty
            )->int:
        if property == IntProperty.SCOPE_WEIGHT:
            return self.m_weight
        elif property == IntProperty.COVER_GOAL:
            return self.m_goal
        elif property == IntProperty.SCOPE_SOURCE_TYPE:
            return self.m_source_type
        elif property == IntProperty.SCOPE_IS_UNDER_DU:
            # TODO: need to detect
            return self.m_is_under_du
        else:
            return super().getIntProperty(coverindex, property)
    
    def setIntProperty(
            self,
            coverindex : int,
            property : IntProperty,
            value : int):
        if property == IntProperty.SCOPE_WEIGHT:
            self.m_weight = value
        elif property == IntProperty.COVER_GOAL:
            self.m_goal = value
        elif property == IntProperty.SCOPE_SOURCE_TYPE:
            self.m_source_type = value
        else:
            super().setIntProperty(coverindex, property, value)    
            
    def createCovergroup(self, 
        name:str, 
        srcinfo:SourceInfo, 
        weight:int, 
        source)->'Covergroup':
        from .mem_covergroup import MemCovergroup
        ret = MemCovergroup(
            self,
            name,
            srcinfo,
            weight,
            source)
        self.addChild(ret)
        return ret
    
    def createNextCover(self, 
        name:str, 
        data:CoverData, 
        sourceinfo:SourceInfo)->CoverIndex:
        ret = MemCoverIndex(name, data, sourceinfo)
        self.m_cover_items.append(ret)
        return ret

    def createScope(self,
                name : str,
                srcinfo : SourceInfo,
                weight : int,
                source,
                type : ScopeTypeT,
                flags):
        # Creates a type scope and associates source information with it
        if ScopeTypeT.DU_ANY(type):
            ret = MemScope(self, name, srcinfo, weight,
                              source, type, flags)
        elif type == ScopeTypeT.COVERGROUP:
            from .mem_covergroup import MemCovergroup
            ret = MemCovergroup(self, name, srcinfo, weight,source)
        elif type == ScopeTypeT.COVERINSTANCE:
            from .mem_covergroup import MemCovergroup
            ret = MemCovergroup(self, name, srcinfo, weight,source)
            ret.m_type = ScopeTypeT.COVERINSTANCE
        elif type == ScopeTypeT.COVERPOINT:
            from .mem_coverpoint import MemCoverpoint
            ret = MemCoverpoint(self, name, srcinfo, weight, source)
#         elif type == ScopeTypeT.CROSS:
#             from .mem_cross import MemCross
#             ret = MemCross(self, name, srcinfo, weight, source)
        else:
            raise NotImplementedError("Scope type " + str(type) + " not supported")
        
        self.addChild(ret)
        
        return ret            
    
    def createInstance(self,
                    name : str,
                    fileinfo : SourceInfo,
                    weight : int,
                    source : SourceT,
                    type : ScopeTypeT,
                    du_scope : 'Scope',
                    flags : FlagsT) ->'Scope':
        # Create an instance of a type scope
        from ucis.mem.mem_instance_scope import MemInstanceScope
        ret = MemInstanceScope(self, name, fileinfo, weight, source, type, du_scope, flags)
        self.addChild(ret)
        return ret
    
    def createToggle(self,
                    name : str,
                    canonical_name : str,
                    flags : FlagsT,
                    toggle_metric : ToggleMetricT,
                    toggle_type : ToggleTypeT,
                    toggle_dir : ToggleDirT) -> 'Scope':
        raise UnimplError()            
    
    def scopes(self, mask)->Iterator['Scope']:
        return MemScopeIterator(self.m_children, mask)
    
    def coverItems(self, mask : CoverTypeT) -> Iterator[CoverIndex]:
        return MemCoverIndexIterator(self.m_cover_items, mask)
    
