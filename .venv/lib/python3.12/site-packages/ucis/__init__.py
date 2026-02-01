
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
from enum import IntEnum, auto
from .report import *
from .rgy import *
from .ucis import UCIS
from .scope import Scope

from .handle_property import HandleProperty
from .history_node import HistoryNode
from .history_node_kind import HistoryNodeKind
from .int_property import IntProperty
from .obj import Obj
from ucis.real_property import RealProperty
from ucis.source_info import SourceInfo
from ucis.str_property import StrProperty
from ucis.test_data import TestData
from ucis.test_status_t import TestStatusT
from ucis.source_t import SourceT
from ucis.flags_t import FlagsT
from ucis.scope_type_t import ScopeTypeT
from ucis.cover_type_t import CoverTypeT
from ucis.cover_flags_t import CoverFlagsT
from ucis.cover_data import CoverData
from ucis.toggle_metric_t import ToggleMetricT
from ucis.toggle_type_t import ToggleTypeT
from ucis.toggle_dir_t import ToggleDirT
from _datetime import datetime


#********************************************************************
#* Property Functions
#********************************************************************
# Global declarations    
UCIS_INT_IS_MODIFIED = IntProperty.IS_MODIFIED
UCIS_INT_MODIFIED_SINCE_SIM = IntProperty.MODIFIED_SINCE_SIM
UCIS_INT_NUM_TESTS = IntProperty.NUM_TESTS
UCIS_INT_SCOPE_WEIGHT = IntProperty.SCOPE_WEIGHT
UCIS_INT_SCOPE_GOAL = IntProperty.SCOPE_GOAL
UCIS_INT_SCOPE_SOURCE_TYPE = IntProperty.SCOPE_SOURCE_TYPE
UCIS_INT_NUM_CROSSED_CVPS = IntProperty.NUM_CROSSED_CVPS
UCIS_INT_SCOPE_IS_UNDER_DU = IntProperty.SCOPE_IS_UNDER_DU
UCIS_INT_SCOPE_IS_UNDER_COVERINSTANCE = IntProperty.SCOPE_IS_UNDER_COVERINSTANCE
UCIS_INT_SCOPE_NUM_COVERITEMS = IntProperty.SCOPE_NUM_COVERITEMS
UCIS_INT_SCOPE_NUM_EXPR_TERMS = IntProperty.SCOPE_NUM_EXPR_TERMS
UCIS_INT_TOGGLE_TYPE = IntProperty.TOGGLE_TYPE
UCIS_INT_TOGGLE_DIR = IntProperty.TOGGLE_DIR
UCIS_INT_TOGGLE_COVERED = IntProperty.TOGGLE_COVERED
UCIS_INT_BRANCH_HAS_ELSE = IntProperty.BRANCH_HAS_ELSE
UCIS_INT_BRANCH_ISCASE = IntProperty.BRANCH_ISCASE
UCIS_INT_COVER_GOAL = IntProperty.COVER_GOAL
UCIS_INT_COVER_LIMIT = IntProperty.COVER_LIMIT
UCIS_INT_COVER_WEIGHT = IntProperty.COVER_WEIGHT
UCIS_INT_TEST_STATUS = IntProperty.TEST_STATUS
UCIS_INT_TEST_COMPULSORY = IntProperty.TEST_COMPULSORY
UCIS_INT_STMT_INDEX = IntProperty.STMT_INDEX
UCIS_INT_BRANCH_COUNT = IntProperty.BRANCH_COUNT
UCIS_INT_FSM_STATEVAL = IntProperty.FSM_STATEVAL
UCIS_INT_CVG_ATLEAST = IntProperty.CVG_ATLEAST
UCIS_INT_CVG_AUTOBINMAX = IntProperty.CVG_AUTOBINMAX
UCIS_INT_CVG_DETECTOVERLAP = IntProperty.CVG_DETECTOVERLAP
UCIS_INT_CVG_NUMPRINTMISSING = IntProperty.CVG_NUMPRINTMISSING
UCIS_INT_CVG_STROBE = IntProperty.CVG_STROBE
UCIS_INT_CVG_PERINSTANCE = IntProperty.CVG_PERINSTANCE
UCIS_INT_CVG_GETINSTCOV = IntProperty.CVG_GETINSTCOV
UCIS_INT_CVG_MERGEINSTANCES = IntProperty.CVG_MERGEINSTANCES

UCIS_STR_FILE_NAME = StrProperty.FILE_NAME
UCIS_STR_SCOPE_NAME = StrProperty.SCOPE_NAME
UCIS_STR_SCOPE_HIER_NAME = StrProperty.SCOPE_HIER_NAME
UCIS_STR_INSTANCE_DU_NAME = StrProperty.INSTANCE_DU_NAME
UCIS_STR_UNIQUE_ID = StrProperty.UNIQUE_ID
UCIS_STR_VER_STANDARD = StrProperty.VER_STANDARD
UCIS_STR_VER_STANDARD_VERSION = StrProperty.VER_STANDARD_VERSION
UCIS_STR_VER_VENDOR_ID = StrProperty.VER_VENDOR_ID
UCIS_STR_VER_VENDOR_TOOL = StrProperty.VER_VENDOR_TOOL
UCIS_STR_VER_VENDOR_VERSION = StrProperty.VER_VENDOR_VERSION
UCIS_STR_GENERIC = StrProperty.GENERIC
UCIS_STR_ITH_CROSSED_CVP_NAME = StrProperty.ITH_CROSSED_CVP_NAME
UCIS_STR_HIST_CMDLINE = StrProperty.HIST_CMDLINE
UCIS_STR_HIST_RUNCWD = StrProperty.HIST_RUNCWD
UCIS_STR_COMMENT = StrProperty.COMMENT
UCIS_STR_TEST_TIMEUNIT = StrProperty.TEST_TIMEUNIT
UCIS_STR_TEST_DATE = StrProperty.TEST_DATE
UCIS_STR_TEST_SIMARGS = StrProperty.TEST_SIMARGS
UCIS_STR_TEST_USERNAME = StrProperty.TEST_USERNAME
UCIS_STR_TEST_NAME = StrProperty.TEST_NAME
UCIS_STR_TEST_SEED = StrProperty.TEST_SEED
UCIS_STR_TEST_HOSTNAME = StrProperty.TEST_HOSTNAME
UCIS_STR_TEST_HOSTOS = StrProperty.TEST_HOSTOS
UCIS_STR_EXPR_TERMS = StrProperty.EXPR_TERMS
UCIS_STR_TOGGLE_CANON_NAME = StrProperty.TOGGLE_CANON_NAME
UCIS_STR_UNIQUE_ID_ALIAS = StrProperty.UNIQUE_ID_ALIAS
UCIS_STR_DESIGN_VERSION_ID = StrProperty.DESIGN_VERSION_ID
UCIS_STR_DU_SIGNATURE = StrProperty.DU_SIGNATURE
UCIS_STR_HIST_TOOLCATEGORY = StrProperty.HIST_TOOLCATEGORY
UCIS_STR_HIST_LOG_NAME = StrProperty.HIST_LOG_NAME
UCIS_STR_HIST_PHYS_NAME = StrProperty.HIST_PHYS_NAME    

UCIS_TESTSTATUS_OK = TestStatusT.OK
UCIS_TESTSTATUS_WARNING = TestStatusT.WARNING    #/* test warning ($warning called) */
UCIS_TESTSTATUS_ERROR = TestStatusT.ERROR      #/* test error ($error called) */
UCIS_TESTSTATUS_FATAL = TestStatusT.FATAL      #/* fatal test error ($fatal called) */
UCIS_TESTSTATUS_MISSING = TestStatusT.MISSING         #/* test not run yet */
UCIS_TESTSTATUS_MERGE_ERROR = TestStatusT.MERGE_ERROR #/* testdata record was merged with inconsistent data values */

UCIS_HISTORYNODE_NONE   = HistoryNodeKind.NONE
UCIS_HISTORYNODE_ALL    = HistoryNodeKind.ALL
UCIS_HISTORYNODE_TEST   = HistoryNodeKind.TEST
UCIS_HISTORYNODE_MERGE  = HistoryNodeKind.MERGE

UCIS_VHDL = SourceT.VHDL
UCIS_VLOG = SourceT.VLOG
UCIS_SV = SourceT.SV
UCIS_SYSTEMC = SourceT.SYSTEMC
UCIS_PSL_VHDL = SourceT.PSL_VHDL
UCIS_PSL_VLOG = SourceT.PSL_VLOG
UCIS_PSL_SV = SourceT.PSL_SV
UCIS_PSL_SYSTEMC = SourceT.PSL_SYSTEMC
UCIS_E = SourceT.E
UCIS_VERA = SourceT.VERA
UCIS_NONE = SourceT.NONE
UCIS_OTHER = SourceT.OTHER
UCIS_SOURCE_ERROR = SourceT.SOURCE_ERROR
    
UCIS_TOGGLE = ScopeTypeT.TOGGLE
UCIS_BRANCH = ScopeTypeT.BRANCH
UCIS_EXPR = ScopeTypeT.EXPR
UCIS_COND = ScopeTypeT.COND
UCIS_INSTANCE = ScopeTypeT.INSTANCE
UCIS_PROCESS = ScopeTypeT.PROCESS
UCIS_BLOCK = ScopeTypeT.BLOCK
UCIS_FUNCTION = ScopeTypeT.FUNCTION
UCIS_FORKJOIN = ScopeTypeT.FORKJOIN
UCIS_GENERATE = ScopeTypeT.GENERATE
UCIS_GENERIC = ScopeTypeT.GENERIC
UCIS_CLASS = ScopeTypeT.CLASS
UCIS_COVERGROUP = ScopeTypeT.COVERGROUP
UCIS_COVERINSTANCE = ScopeTypeT.COVERINSTANCE
UCIS_COVERPOINT = ScopeTypeT.COVERPOINT
UCIS_CROSS = ScopeTypeT.CROSS
UCIS_COVER = ScopeTypeT.COVER
UCIS_ASSERT = ScopeTypeT.ASSERT
UCIS_PROGRAM = ScopeTypeT.PROGRAM
UCIS_PACKAGE = ScopeTypeT.PACKAGE
UCIS_TASK = ScopeTypeT.TASK
UCIS_INTERFACE = ScopeTypeT.INTERFACE
UCIS_FSM = ScopeTypeT.FSM
UCIS_DU_MODULE = ScopeTypeT.DU_MODULE
UCIS_DU_ARCH = ScopeTypeT.DU_ARCH
UCIS_DU_PACKAGE = ScopeTypeT.DU_PACKAGE
UCIS_DU_PROGRAM = ScopeTypeT.DU_PROGRAM
UCIS_DU_INTERFACE = ScopeTypeT.DU_INTERFACE
UCIS_FSM_STATES = ScopeTypeT.FSM_STATES
UCIS_FSM_TRANS = ScopeTypeT.FSM_TRANS
UCIS_COVBLOCK = ScopeTypeT.COVBLOCK
UCIS_CVGBINSCOPE = ScopeTypeT.CVGBINSCOPE
UCIS_ILLEGALBINSCOPE = ScopeTypeT.ILLEGALBINSCOPE
UCIS_IGNOREBINSCOPE = ScopeTypeT.IGNOREBINSCOPE
UCIS_RESERVEDSCOPE = ScopeTypeT.RESERVEDSCOPE
UCIS_SCOPE_ERROR = ScopeTypeT.SCOPE_ERROR

UCIS_INST_ONCE = FlagsT.INST_ONCE
UCIS_ENABLED_STMT = FlagsT.ENABLED_STMT
UCIS_ENABLED_BRANCH = FlagsT.ENABLED_BRANCH
UCIS_ENABLED_COND = FlagsT.ENABLED_COND
UCIS_ENABLED_EXPR = FlagsT.ENABLED_EXPR
UCIS_ENABLED_FSM = FlagsT.ENABLED_FSM
UCIS_ENABLED_TOGGLE = FlagsT.ENABLED_TOGGLE
UCIS_SCOPE_UNDER_DU = FlagsT.SCOPE_UNDER_DU
UCIS_SCOPE_EXCLUDED = FlagsT.SCOPE_EXCLUDED
UCIS_SCOPE_PRAGMA_EXCLUDED = FlagsT.SCOPE_PRAGMA_EXCLUDED
UCIS_SCOPE_PRAGMA_CLEARED = FlagsT.SCOPE_PRAGMA_CLEARED
UCIS_SCOPE_SPECIALIZED = FlagsT.SCOPE_SPECIALIZED
UCIS_UOR_SAFE_SCOPE = FlagsT.UOR_SAFE_SCOPE
UCIS_UOR_SAFE_SCOPE_ALLCOVERS = FlagsT.UOR_SAFE_SCOPE_ALLCOVERS
UCIS_IS_TOP_NODE = FlagsT.IS_TOP_NODE
UCIS_IS_IMMEDIATE_ASSERT = FlagsT.IS_IMMEDIATE_ASSERT
UCIS_SCOPE_CVG_AUTO = FlagsT.SCOPE_CVG_AUTO
UCIS_SCOPE_CVG_SCALAR = FlagsT.SCOPE_CVG_SCALAR
UCIS_SCOPE_CVG_VECTOR = FlagsT.SCOPE_CVG_VECTOR
UCIS_SCOPE_CVG_TRANSITION = FlagsT.SCOPE_CVG_TRANSITION
UCIS_SCOPE_IFF_EXISTS = FlagsT.SCOPE_IFF_EXISTS
UCIS_ENABLED_BLOCK = FlagsT.ENABLED_BLOCK
UCIS_SCOPE_BLOCK_ISBRANCH = FlagsT.SCOPE_BLOCK_ISBRANCH


UCIS_CVGBIN      = CoverTypeT.CVGBIN
UCIS_COVERBIN    = CoverTypeT.COVERBIN
UCIS_ASSERTBIN   = CoverTypeT.ASSERTBIN
UCIS_STMTBIN     = CoverTypeT.STMTBIN
UCIS_BRANCHBIN   = CoverTypeT.BRANCHBIN
UCIS_EXPRBIN     = CoverTypeT.EXPRBIN
UCIS_CONDBIN     = CoverTypeT.CONDBIN
UCIS_TOGGLEBIN   = CoverTypeT.TOGGLEBIN
UCIS_PASSBIN     = CoverTypeT.PASSBIN
UCIS_FSMBIN      = CoverTypeT.FSMBIN
UCIS_USERBIN     = CoverTypeT.USERBIN
UCIS_GENERICBIN  = CoverTypeT.GENERICBIN
UCIS_COUNT       = CoverTypeT.COUNT
UCIS_FAILBIN     = CoverTypeT.FAILBIN
UCIS_VACUOUSBIN  = CoverTypeT.VACUOUSBIN
UCIS_DISABLEDBIN = CoverTypeT.DISABLEDBIN
UCIS_ATTEMPTBIN  = CoverTypeT.ATTEMPTBIN
UCIS_ACTIVEBIN   = CoverTypeT.ACTIVEBIN
UCIS_IGNOREBIN   = CoverTypeT.IGNOREBIN
UCIS_ILLEGALBIN  = CoverTypeT.ILLEGALBIN
UCIS_DEFAULTBIN  = CoverTypeT.DEFAULTBIN
UCIS_PEAKACTIVEBIN = CoverTypeT.PEAKACTIVEBIN
UCIS_BLOCKBIN    = CoverTypeT.BLOCKBIN
UCIS_USERBITS    = CoverTypeT.USERBITS
UCIS_RESERVEDBIN = CoverTypeT.RESERVEDBIN

UCIS_CVGBIN = CoverTypeT.CVGBIN
UCIS_COVERBIN = CoverTypeT.COVERBIN
UCIS_ASSERTBIN = CoverTypeT.ASSERTBIN
UCIS_STMTBIN = CoverTypeT.STMTBIN

UCIS_IS_32BIT = CoverFlagsT.IS_32BIT
UCIS_IS_64BIT = CoverFlagsT.IS_64BIT
UCIS_IS_VECTOR = CoverFlagsT.IS_VECTOR
UCIS_HAS_GOAL = CoverFlagsT.HAS_GOAL
UCIS_HAS_WEIGHT = CoverFlagsT.HAS_WEIGHT

UCIS_TOGGLE_METRIC_NOBINS      = ToggleMetricT.NOBINS
UCIS_TOGGLE_METRIC_ENUM        = ToggleMetricT.ENUM
UCIS_TOGGLE_METRIC_TRANSITION  = ToggleMetricT.TRANSITION
UCIS_TOGGLE_METRIC_2STOGGLE    = ToggleMetricT._2STOGGLE
UCIS_TOGGLE_METRIC_ZTOGGLE     = ToggleMetricT.ZTOGGLE
UCIS_TOGGLE_METRIC_XTOGGLE     = ToggleMetricT.XTOGGLE

UCIS_TOGGLE_TYPE_NET = ToggleTypeT.NET
UCIS_TOGGLE_TYPE_REG = ToggleTypeT.REG

UCIS_TOGGLE_DIR_INTERNAL = ToggleDirT.INTERNAL
UCIS_TOGGLE_DIR_IN       = ToggleDirT.IN
UCIS_TOGGLE_DIR_OUT      = ToggleDirT.OUT
UCIS_TOGGLE_DIR_INOUT    = ToggleDirT.INOUT

    
def ucis_GetIntProperty(
        db : UCIS,
        obj : Obj,
        coverindex : int,
        property : IntProperty
        ) -> int:
    if obj is not None:
        return obj.getIntProperty(coverindex, property)
    else:
        return db.getIntProperty(coverindex, property)
    
def ucis_SetIntProperty(
        db : UCIS,
        obj : Obj,
        coverindex : int,
        property : IntProperty,
        value : int
        ):
    if obj is not None:
        obj.setIntProperty(coverindex, property, value)
    else:
        db.setIntProperty(coverindex, property, value)
        
def ucis_GetRealProperty(
        db : UCIS,
        obj : Obj,
        coverindex : int,
        property : RealProperty
        ) -> float:
    if obj is not None:
        return obj.getRealProperty(coverindex, property)
    else:
        return db.getRealProperty(coverindex, property)
    
def ucis_SetRealProperty(
        db : UCIS,
        obj : Obj,
        coverindex : int,
        property : RealProperty,
        value : float
        ):
    if obj is not None:
        obj.setRealProperty(coverindex, property, value)
    else:
        db.setRealProperty(coverindex, property, value)

def ucis_GetStringProperty(
        db : UCIS,
        obj : Obj,
        coverindex : int,
        property : StrProperty
        ) -> str:
    if obj is not None:
        return obj.getStringProperty(coverindex, property)
    else:
        return db.getStringProperty(coverindex, property)
    
def ucis_SetStringProperty(
        db : UCIS,
        obj : Obj,
        coverindex : int,
        property : StrProperty,
        value : str
        ):
    if obj is not None:
        obj.setStringProperty(coverindex, property, value)
    else:
        db.setStringProperty(coverindex, property, value)
        
def ucis_GetHandleProperty(
        db : UCIS,
        obj : Obj,
        coverindex : int,
        property : HandleProperty
        ) -> Scope:
    if obj is not None:
        return obj.getHandleProperty(coverindex, property)
    else:
        return db.getHandleProperty(coverindex, property)
    
def ucis_SetHandleProperty(
        db : UCIS,
        obj : Obj,
        coverindex : int,
        property : HandleProperty,
        value : Scope
        ):
    if obj is not None:
        obj.setHandleProperty(coverindex, property, value)
    else:
        db.setHandleProperty(coverindex, property, value)        
        
def ucis_CreateScope(
        db : UCIS,
        parent : Scope,
        name : str,
        sourceinfo : SourceInfo,
        weight : int,
        source : SourceT,
        type : ScopeTypeT,
        flags) -> Scope:
    if parent is not None:
        return parent.createScope(name, sourceinfo, weight, source, type, flags)
    else:
        return db.createScope(name, sourceinfo, weight, source, type, flags)
    
def ucis_CreateInstance(
        db : UCIS,
        parent : Scope,
        name : str,
        fileinfo : SourceInfo,
        weight : int,
        source : SourceT,
        type : ScopeTypeT,
        du_scope : Scope,
        flags : FlagsT) ->Scope:
    logging.debug("ucis_CreateInstance: parent=" + str(parent))
    if parent is not None:
        return parent.createInstance(name, fileinfo, weight, source, type, du_scope, flags)
    else:
        return db.createInstance(name, fileinfo, weight, source, type, du_scope, flags)
   
def ucis_CreateToggle(
        db : UCIS,
        parent : Scope,
        name : str,
        canonical_name : str,
        flags : FlagsT,
        toggle_metric : ToggleMetricT,
        toggle_type : ToggleTypeT,
        toggle_dir : ToggleDirT) ->Scope:
    if parent is not None:
        return parent.createToggle(name, canonical_name, flags,
                                   toggle_metric, toggle_type, toggle_dir)
    else:
        return db.createToggle(name, canonical_name, flags,
                                   toggle_metric, toggle_type, toggle_dir)

def ucis_CreateNextCover(
        db : UCIS,
        parent : Scope,
        name : str,
        data : CoverData,
        sourceinfo : SourceInfo) ->int:
    return parent.createNextCover(name, data, sourceinfo)

def ucis_RemoveScope(
        db : UCIS,
        scope : Scope) -> int:
    return db.removeScope(scope)

def ucis_CreateHistoryNode(
    db : UCIS,
    parent : HistoryNode,
    logicalname,   #/* primary key, never NULL */
    physicalname,
    kind : HistoryNodeKind):
    # TODO: what if parent is non-null?
    return db.createHistoryNode(parent, logicalname, physicalname, kind)

def ucis_CreateFileHandle (
    db : UCIS,
    filename : str,
    fileworkdir : str):
    return db.createFileHandle(filename, fileworkdir)

def ucis_SetTestData(
    db : UCIS,
    testhistorynode : HistoryNode,
    testdata : TestData):
    testhistorynode.setTestData(testdata)
    
def ucis_Write(
        db : UCIS,
        file : str,
        scope : Scope,
        recurse : int,
        covertype : CoverTypeT) ->int:
#    try:
    db.write(
        file, 
        scope, 
        recurse==1, 
        covertype)
    return 0
#    except Exception as e:
#        return -1
    
def ucis_Close(db : UCIS) ->int:
    db.close()
    return 0

def ucis_Time():
    """Current time in UCIS Y/M/D/H/M/S format"""
    return datetime.now().strftime("%Y%m%d%H%M%S")
