
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


class StrProperty(IntEnum):
    FILE_NAME = 0 #/* UCISDB file/directory name (read only) */
    SCOPE_NAME = auto() #/* Scope name */
    SCOPE_HIER_NAME = auto() #/* Hierarchical scope name */
    INSTANCE_DU_NAME = auto() #/* Instance' design unit name */
    UNIQUE_ID = auto() #/* Scope or coveritem unique-id (read only) */
    VER_STANDARD = auto() #/* Standard (Currently fixed to be "UCIS") */
    VER_STANDARD_VERSION = auto() #/* Version of standard (e.g. "2011", etc) */
    VER_VENDOR_ID = auto() #/* Vendor id (e.g. "CDNS", "MENT", "SNPS", etc) */
    VER_VENDOR_TOOL = auto() #/* Vendor tool (e.g. "Incisive", "Questa", "VCS", etc) */
    VER_VENDOR_VERSION = auto() #/* Vendor tool version (e.g. "6.5c", "Jun-12-2009", etc) */
    GENERIC = auto() #/* Miscellaneous string data */
    ITH_CROSSED_CVP_NAME = auto() #/* Ith coverpoint name of a cross */
    HIST_CMDLINE = auto() #/* Test run command line */
    HIST_RUNCWD = auto() #/* Test run working directory */
    COMMENT = auto() #/* Comment */
    TEST_TIMEUNIT = auto() #/* Test run simulation time unit */
    TEST_DATE = auto() #/* Test run date */
    TEST_SIMARGS = auto() #/* Test run simulator arguments */
    TEST_USERNAME = auto() #/* Test run user name */
    TEST_NAME = auto() #/* Test run name */
    TEST_SEED = auto() #/* Test run seed */
    TEST_HOSTNAME = auto() #/* Test run hostname */
    TEST_HOSTOS = auto() #/* Test run hostOS */
    EXPR_TERMS = auto() #/* Input ordered expr term strings delimited by '#' */
    TOGGLE_CANON_NAME = auto() #/* Toggle object canonical name */
    UNIQUE_ID_ALIAS = auto() #/* Scope or coveritem unique-id alias */
    DESIGN_VERSION_ID = auto() #/* Version of the design or elaboration-id */
    DU_SIGNATURE = auto()
    HIST_TOOLCATEGORY = auto()
    HIST_LOG_NAME = auto()
    HIST_PHYS_NAME = auto()
