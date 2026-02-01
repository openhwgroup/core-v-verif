
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
Created on Jan 11, 2020

@author: ballance
'''
from ucis.obj import Obj
from ucis.int_property import IntProperty
from ucis.real_property import RealProperty
from ucis.str_property import StrProperty
from ucis.handle_property import HandleProperty
from ucis.lib.libucis import get_lib

class LibObj(Obj):
    
    def __init__(self, db, obj):
        self.db = db
        self.obj = obj

    def getIntProperty(
            self, 
            coverindex : int,
            property : IntProperty
            )->int:
        raise NotImplementedError()
    
    def setIntProperty(
            self,
            coverindex : int,
            property : IntProperty,
            value : int):
        obj = self.db if self.obj is None else self.obj
        get_lib().ucis_SetIntProperty(self.db, obj, coverindex, property, value)

    def getRealProperty(
            self,
            coverindex : int,
            property : RealProperty) -> float:
        raise NotImplementedError()
        
    def setRealProperty(
            self,
            coverindex : int,
            property : RealProperty,
            value : float):
        raise NotImplementedError()

    def getStringProperty(
            self,
            coverindex : int,
            property : StrProperty) -> str:
        raise NotImplementedError()
    
    def setStringProperty(
            self,
            coverindex : int,
            property : StrProperty,
            value : str):
        obj = self.db if self.obj is None else self.obj
        get_lib().ucis_SetStringProperty(
            self.db, 
            obj, 
            coverindex, 
            property, 
            str.encode(value))
        
    def getHandleProperty(
            self,
            coverindex : int,
            property : HandleProperty) -> 'Scope':
        raise NotImplementedError()
    
    def setHandleProperty(
            self,
            coverindex : int,
            property : HandleProperty,
            value : 'Scope'):
        raise NotImplementedError()        