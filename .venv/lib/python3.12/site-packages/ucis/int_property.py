
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
Created on Jan 9, 2020

@author: ballance
'''
from enum import IntEnum, auto


class IntProperty(IntEnum):
    IS_MODIFIED = 0 # Modified since opening stored UCISDB (In-memory and read only)
    MODIFIED_SINCE_SIM = auto() # Modified since end of simulation run (In-memory and read only)
    NUM_TESTS = auto() # Number of test history nodes (UCIS_HISTORYNODE_TEST) in UCISDB 
    SCOPE_WEIGHT = auto() # Scope weight 
    SCOPE_GOAL = auto() # Scope goal 
    SCOPE_SOURCE_TYPE = auto() # Scope source type (ucisSourceT) 
    NUM_CROSSED_CVPS = auto() # Number of coverpoints in a cross (read only) 
    SCOPE_IS_UNDER_DU = auto() # Scope is underneath design unit scope (read only) 
    SCOPE_IS_UNDER_COVERINSTANCE = auto() # Scope is underneath covergroup instance (read only) 
    SCOPE_NUM_COVERITEMS = auto() # Number of coveritems underneath scope (read only) 
    SCOPE_NUM_EXPR_TERMS = auto() # Number of input ordered expr term strings delimited by '#' 
    TOGGLE_TYPE = auto() # Toggle type (ucisToggleTypeT) 
    TOGGLE_DIR = auto() # Toggle direction (ucisToggleDirT) 
    TOGGLE_COVERED = auto() # Toggle object is covered 
    BRANCH_HAS_ELSE = auto() # Branch has an 'else' coveritem 
    BRANCH_ISCASE = auto() # Branch represents 'case' statement 
    COVER_GOAL = auto() # Coveritem goal 
    COVER_LIMIT = auto() # Coverage count limit for coveritem 
    COVER_WEIGHT = auto() # Coveritem weight 
    TEST_STATUS = auto() # Test run status (ucisTestStatusT) 
    TEST_COMPULSORY = auto() # Test run is compulsory 
    STMT_INDEX = auto() # Index or number of statement on a line 
    BRANCH_COUNT = auto() # Total branch execution count 
    FSM_STATEVAL = auto() # FSM state value 
    CVG_ATLEAST = auto() # Covergroup at_least option 
    CVG_AUTOBINMAX = auto() # Covergroup auto_bin_max option 
    CVG_DETECTOVERLAP = auto() # Covergroup detect_overlap option 
    CVG_NUMPRINTMISSING = auto() # Covergroup cross_num_print_missing option 
    CVG_STROBE = auto() # Covergroup strobe option 
    CVG_PERINSTANCE = auto() # Covergroup per_instance option 
    CVG_GETINSTCOV = auto() # Covergroup get_inst_coverage option 
    CVG_MERGEINSTANCES = auto() # Covergroup merge_instances option     
    
    
    
    