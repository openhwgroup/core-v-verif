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
from typing import List
from ucis.coverpoint import Coverpoint
from ucis.source_t import SourceT
'''
Created on Dec 22, 2019

@author: ballance
'''

from ucis.cover_type import CoverType
from ucis.cvg_scope import CvgScope
from ucis.int_property import IntProperty
from ucis.scope import Scope
from ucis.source_info import SourceInfo


class Covergroup(CvgScope):
    
    def __init__(self):
        super().__init__()
        # Call set-attr methods to establish defaults
        self.setPerInstance(False)
        self.setMergeInstances(True)
        self.setGetInstCoverage(False)
        # Comment doesn't seem valid on a CvgScope standalone
        self.setComment("")
        pass
    

    def getPerInstance(self)->bool:
        raise NotImplementedError()
    
    def setPerInstance(self, perinst):
        raise NotImplementedError()
    
    def getGetInstCoverage(self) -> bool:
        raise NotImplementedError()
    
    def setGetInstCoverage(self, s : bool):
        raise NotImplementedError()
    
    def getMergeInstances(self)->bool:
        raise NotImplementedError()
    
    def setMergeInstances(self, m:bool):
        raise NotImplementedError()
    
        

    def createCoverpoint(self,
                         name : str,
                         srcinfo : SourceInfo,
                         weight : int,
                         source) -> CoverType:
        raise NotImplementedError()
    
    def createCross(self, 
                    name : str, 
                    srcinfo : SourceInfo,
                    weight : int,
                    source : SourceT, 
                    points_l : List['Coverpoint']) -> CoverType:
        raise NotImplementedError()
    
    def createCoverInstance(
            self,
            name:str,
            srcinfo:SourceInfo,
            weight:int,
            source)->'Covergroup':
        raise NotImplementedError()
    
    def getIntProperty(
        self, 
        coverindex:int, 
        property:IntProperty)->int:
        if property == IntProperty.CVG_PERINSTANCE:
            return 1 if self.getPerInstance() else 0
        elif property == IntProperty.CVG_MERGEINSTANCES:
            return 1 if self.getMergeInstances() else 0
        else:
            return super().getIntProperty(coverindex, property)

    def setIntProperty(
        self, 
        coverindex:int, 
        property:IntProperty, 
        value:int):
        if property == IntProperty.CVG_PERINSTANCE:
            self.setPerInstance(value==1)
        elif property == IntProperty.CVG_MERGEINSTANCES:
            self.setMergeInstances(value==1)
        else:
            super().setIntProperty(coverindex, property, value)

        
    