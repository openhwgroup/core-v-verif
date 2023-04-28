# Copyright 2023 Silicon Laboratories Inc.
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
# not use this file except in compliance with the License, or, at your option,
# the Apache License version 2.0.
#
# You may obtain a copy of the License at
# https://solderpad.org/licenses/SHL-2.1/
#
# Unless required by applicable law or agreed to in writing, any work
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#
# See the License for the specific language governing permissions and
# limitations under the License.

ifndef CV_CORE
  $(error Must set CV_CORE to a valid core)
endif

ifeq ($(CV_CORE),cv32e40x)
  VERIF_ENV_GITDIR = cv32e40x/.git
  VERIF_ENV_REPO ?= https://github.com/silabs-robin/core-v-verif.git
  VERIF_ENV_BRANCH ?= cv32e40xdev_subtree_gitmerge
  #leave these unset for cores that don't clone in verif environments
endif

default:
	@echo read the makefile

comp test hex: $(VERIF_ENV_GITDIR)
	@echo "Command: $(MAKECMDGOALS)"
	make -C $(abspath ./$(CV_CORE)/sim/uvmt) $(MAKECMDGOALS)

$(CV_CORE)/.git:
	@echo cloning verif env repo
	rm -rf $(CV_CORE)
	git clone  -b $(VERIF_ENV_BRANCH)  $(VERIF_ENV_REPO)  $(CV_CORE)
	echo $(CV_CORE) >> .git/info/exclude
	git ls-files $(CV_CORE) | xargs git update-index --skip-worktree

no-skip-worktree:
	sed -i "/^$(CV_CORE)$$/d" .git/info/exclude
	git ls-files -t | grep '^S' | awk '{print $$2}' | xargs git update-index --no-skip-worktree
