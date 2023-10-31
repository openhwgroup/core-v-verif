# Copyright 2022 Silicon Labs, Inc.
# Copyright 2022 OpenHW Group
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://solderpad.org/licenses/
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0


# Defines and Includes

CORE_V_VERIF ?= $(realpath ../..)
CV_CORE      ?= cv32e40s

include  $(CORE_V_VERIF)/$(CV_CORE)/sim/ExternalRepos.mk
include  $(CORE_V_VERIF)/mk/fv/fv.mk


# Options

JG_EXTRAS  = -bg dimgray -fg lightgray

export FV_DEFINES = ${USER_DEFINES}
export FV_INCDIRS = ${USER_INCDIRS}
#TODO:silabs-robin This defines system is not perfect.


# Safety Check

ifndef  CV_SIM_PREFIX
  $(warning  CV_SIM_PREFIX undefined)
endif


# Make Targets

jaspergold: jg
jasper: jg
jg:  $(CV_CORE_PKG)
	$(CV_SIM_PREFIX)  jaspergold  $(JG_EXTRAS)  jaspergold.tcl
	# TODO:silabs-robin  Move to "mk/fv/jg.mk"?

qverify: q
questa: q
q:  $(CV_CORE_PKG)
	$(CV_SIM_PREFIX)  qverify  -do qverify.tcl
	# TODO:silabs-robin  Move to "mk/fv/jg.mk"?
