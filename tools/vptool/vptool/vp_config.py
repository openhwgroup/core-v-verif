#############################################################################
#
# Copyright 2022 Thales
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
#############################################################################
#
# Original Authors:
#
#     Zbigniew CHAMSKI (zbigniew.chamski@thalesgroup.com)
#     Vincent MIGAIROU (vincent.migairou@thalesgroup.com)
#
#############################################################################

import re, os, glob, sys
import subprocess

#####################################
#####  GLOBAL VARIABLE DEFINITION
global VP_PLATFORM_TOP_DIR
VP_PLATFORM_TOP_DIR = ""

## Want to load/save db in/from a unique file (False), or with split files, one per Feature(True)
SPLIT_SAVE=True

##########################################################################
##########################################################################
##### PROJECT SETUP

if "PLATFORM_TOP_DIR" in os.environ:    ## Env Variable existence Check
    VP_PLATFORM_TOP_DIR = os.environ['PLATFORM_TOP_DIR']
    PROJECT_NAME = os.environ['PROJECT_NAME']
    SAVED_DB_LOCATION = VP_PLATFORM_TOP_DIR + '/vplan_database/ip_dir/*.pck'
else:
    print("--- Error: Please define PLATFORM_TOP_DIR env variable")
    sys.exit()

#####  Check PLATFORM_TOP_DIR. Should not occur if VP_PLATFORM_TOP_DIR is automatically set to a correct value.
if VP_PLATFORM_TOP_DIR not in os.getcwd():
    print("""\n---Warning: PLATFORM_TOP_DIR env variable is not in line with current directory
---Warning: Please take care default Loaded/Saved DataBase could be from/to another Project
""")

# Location of the Pickle file containing the current IP/Feature lock info.
LOCKED_IP_LOCATION = VP_PLATFORM_TOP_DIR + "/vplan_database/admin/locked_ip.pick"
