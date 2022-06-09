#!/bin/sh

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

# Platform location == root of the example directories
export PLATFORM_TOP_DIR=`readlink -f $(dirname $0)`

# Set project name.
export PROJECT_NAME=cvxif_top

# Run VPTOOL from the IP top dir.
cd $PLATFORM_TOP_DIR
python3 $PLATFORM_TOP_DIR/vptool/vp.py
cd -
