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
from ucis.cover_index import CoverIndex
from ucis.cover_type_t import CoverTypeT

'''
Created on Dec 22, 2019

@author: ballance
'''

from ucis.source_info import SourceInfo
from ucis.obj import Obj
from ucis.int_property import IntProperty
from ucis.scope_type_t import ScopeTypeT
from ucis.flags_t import FlagsT
from ucis.source_t import SourceT
from ucis.cover_data import CoverData
from ucis.toggle_metric_t import ToggleMetricT
from ucis.toggle_type_t import ToggleTypeT
from ucis.toggle_dir_t import ToggleDirT

class Scope(Obj):
    
    def __init__(self):
        self.setGoal(100)

    def createScope(self,
                    name : str,
                    srcinfo : SourceInfo,
                    weight : int,
                    source,
                    type,
                    flags):
        raise NotImplementedError()
    
    def createInstance(self,
                    name : str,
                    fileinfo : SourceInfo,
                    weight : int,
                    source : SourceT,
                    type : ScopeTypeT,
                    du_scope : 'Scope',
                    flags : FlagsT) ->'Scope':
        raise NotImplementedError()
    
    def createToggle(self,
                    name : str,
                    canonical_name : str,
                    flags : FlagsT,
                    toggle_metric : ToggleMetricT,
                    toggle_type : ToggleTypeT,
                    toggle_dir : ToggleDirT) -> 'Scope':
        raise NotImplementedError()
    
    def createCovergroup(self,
                    name : str,
                    srcinfo : SourceInfo,
                    weight : int,
                    source) -> 'Covergroup':
        raise NotImplementedError()
    
    def createNextCover(self,
                        name : str,
                        data : CoverData,
                        sourceinfo : SourceInfo) -> CoverIndex:
        raise NotImplementedError()

    def getWeight(self):
        raise NotImplementedError()
    
    def setWeight(self, w):
        raise NotImplementedError()
    
    def getGoal(self)->int:
        raise NotImplementedError()
    
    def setGoal(self,goal)->int:
        raise NotImplementedError()
    
    def getFlags(self)->FlagsT:
        raise NotImplementedError()
    
    def getScopeType(self)->ScopeTypeT:
        raise NotImplementedError()
    
    def getScopeName(self)->str:
        raise NotImplementedError()
    
    def getSourceInfo(self)->SourceInfo:
        raise NotImplementedError()
    
    def scopes(self, mask : ScopeTypeT) -> Iterator['Scope']:
        raise NotImplementedError()
    
    def coverItems(self, mask : CoverTypeT)-> Iterator['CoverIndex']:
        raise NotImplementedError()
    
    def getIntProperty(
        self, 
        coverindex:int, 
        property:IntProperty)-> int:
        if property == IntProperty.SCOPE_GOAL:
            return self.getGoal()
        else:
            return super().getIntProperty(coverindex, property)
        
    def setIntProperty(
        self, 
        coverindex:int, 
        property:IntProperty, 
        value:int):
        if property == IntProperty.SCOPE_GOAL:
            return self.setGoal(value)
        else:
            super().setIntProperty(coverindex, property, value)
            
    
