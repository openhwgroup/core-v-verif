
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
from ucis.source_file import SourceFile

class StatementId():
    
    def __init__(self, file : SourceFile, line : int, item : int):
        self.file = file
        self.line = line
        self.item = item
        
    def getFile(self) -> SourceFile:
        return self.file
    
    def getLine(self) -> int:
        return self.line
    
    def getItem(self) -> int:
        return self.item
    
    
    