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

class ScopeTypeT(IntFlag):
    
    # /* cover scope- toggle coverage scope: */ \
    TOGGLE = 0x0000000000000001
    # /* cover scope- branch coverage scope: */ \
    BRANCH = 0x0000000000000002
    # /* cover scope- expression coverage scope: */ \
    EXPR = 0x0000000000000004
    #/* cover scope- condition coverage scope: */ \
    COND = 0x0000000000000008
    #/* HDL scope- Design hierarchy instance: */ \
    INSTANCE = 0x0000000000000010
    #/* HDL scope- process: */ \
    PROCESS = 0x0000000000000020
    #/* HDL scope- vhdl block, vlog begin-end: */ \    
    BLOCK = 0x0000000000000040 
    #/* HDL scope- function: */ \
    FUNCTION = 0x0000000000000080
    #/* HDL scope- Verilog fork-join block: */ \
    FORKJOIN = 0x0000000000000100
    #/* HDL scope- generate block: */ \
    GENERATE = 0x0000000000000200
    #/* cover scope- generic scope type: */ \
    GENERIC = 0x0000000000000400
    #/* HDL scope- class type scope: */ \
    CLASS = 0x0000000000000800
    #/* cover scope- covergroup type scope: */ \
    COVERGROUP = 0x0000000000001000
    #/* cover scope- covergroup instance scope: */ \
    COVERINSTANCE = 0x0000000000002000
    #/* cover scope- coverpoint scope: */ \
    COVERPOINT = 0x0000000000004000
    #/* cover scope- cross scope: */ \
    CROSS = 0x0000000000008000
    #/* cover scope- directive(SVA/PSL cover: */ \
    COVER = 0x0000000000010000
    #/* cover scope- directive(SVA/PSL assert: */ \
    ASSERT = 0x0000000000020000
    #/* HDL scope- SV program instance: */ \
    PROGRAM = 0x0000000000040000
    #/* HDL scope- package instance: */ \
    PACKAGE = 0x0000000000080000
    #/* HDL scope- task: */ \
    TASK = 0x0000000000100000
    #/* HDL scope- SV interface instance: */ \
    INTERFACE = 0x0000000000200000
    #/* cover scope- FSM coverage scope: */ \
    FSM = 0x0000000000400000
    #/* design unit- for instance type: */ \
    DU_MODULE = 0x0000000001000000
    #/* design unit- for instance type: */ \
    DU_ARCH = 0x0000000002000000
    #/* design unit- for instance type: */ \
    DU_PACKAGE = 0x0000000004000000
    #/* design unit- for instance type: */ \
    DU_PROGRAM = 0x0000000008000000
    #/* design unit- for instance type: */ \
    DU_INTERFACE = 0x0000000010000000
    #/* cover scope- FSM states coverage scope: */ \
    FSM_STATES = 0x0000000020000000
    #/* cover scope- FSM transition coverage scope: */\
    FSM_TRANS = 0x0000000040000000
    #/* cover scope- block coverage scope: */ \
    COVBLOCK = 0x0000000080000000
    #/* cover scope- SV cover bin scope: */ \
    CVGBINSCOPE = 0x0000000100000000
    #/* cover scope- SV illegal bin scope: */ \
    ILLEGALBINSCOPE = 0x0000000200000000
    #/* cover scope- SV ignore bin scope: */ \
    IGNOREBINSCOPE = 0x0000000400000000
    #
    RESERVEDSCOPE = 0xFF00000000000000
    #/* error return code: */ \
    SCOPE_ERROR = 0x0000000000000000   
    
    ALL = 0x0000FFFFFFFFFFFF
    
    @staticmethod
    def DU_ANY(t):
        return (t & (ScopeTypeT.DU_MODULE|ScopeTypeT.DU_ARCH|ScopeTypeT.DU_PACKAGE|ScopeTypeT.DU_PROGRAM|ScopeTypeT.DU_INTERFACE)) != 0
    