
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
from enum import IntFlag

class FlagsT(IntFlag):
    
    # An instance is instantiated only once; 
    # code coverage is stored only in the instance
    INST_ONCE = 0x00000001
    # statement coverage collected for scope
    ENABLED_STMT = 0x00000002
    # branch coverage coverage collected for scope
    ENABLED_BRANCH = 0x00000004
    # condition coverage coverage collected for scope
    ENABLED_COND = 0x00000008
    # expression coverage coverage    
    ENABLED_EXPR = 0x00000010

    ENABLED_FSM = 0x00000020
    ENABLED_TOGGLE = 0x00000040
    SCOPE_UNDER_DU = 0x00000100
    SCOPE_EXCLUDED = 0x00000200
    SCOPE_PRAGMA_EXCLUDED = 0x00000400
    SCOPE_PRAGMA_CLEARED = 0x00000800
    SCOPE_SPECIALIZED = 0x00001000
    UOR_SAFE_SCOPE = 0x00002000
    UOR_SAFE_SCOPE_ALLCOVERS = 0x00004000
    IS_TOP_NODE = 0x00010000
    IS_IMMEDIATE_ASSERT = 0x00010000
    SCOPE_CVG_AUTO = 0x00010000
    SCOPE_CVG_SCALAR = 0x00020000
    SCOPE_CVG_VECTOR = 0x00040000
    SCOPE_CVG_TRANSITION = 0x00080000
    SCOPE_IFF_EXISTS = 0x00100000
    ENABLED_BLOCK = 0x00800000
    SCOPE_BLOCK_ISBRANCH = 0x01000000

