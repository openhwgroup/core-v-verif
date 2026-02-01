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

#from ucis import UCIS_CVGBIN, UCIS_IS_32BIT, UCIS_HAS_GOAL, UCIS_HAS_WEIGHT
from ucis.cover_type_t import CoverTypeT
from ucis.cover_flags_t import CoverFlagsT
from ucis.cover_data import CoverData
from ucis.cover_index import CoverIndex
from ucis.cvg_scope import CvgScope
from ucis.source_info import SourceInfo


class Coverpoint(CvgScope):
    
    def __init__(self):
        super().__init__()
        self.setComment("")

    def getScopeGoal(self) -> int:
        raise NotImplementedError("getScopeGoal in " + str(type(self)))
    
    def setScopeGoal(self, goal):
        raise NotImplementedError("setScopeGoal in " + str(type(self)))
                
    def createBin(
            self,
            name : str,
            srcinfo : SourceInfo,
            at_least : int,
            count : int,
            rhs : str,
            kind = CoverTypeT.CVGBIN) -> CoverIndex:
        coverdata = CoverData(
            kind,
            (CoverFlagsT.IS_32BIT|CoverFlagsT.HAS_GOAL|CoverFlagsT.HAS_WEIGHT))
        coverdata.data = count
        coverdata.at_least = at_least
        coverdata.goal = 1
        # TODO: bring weight in via API?
        coverdata.weight = 1
        
        index = self.createNextCover(
            name, 
            coverdata,
            srcinfo)
        
        return index        
        