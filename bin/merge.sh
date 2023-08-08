#!/bin/bash

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


#TODO:
#List up the PRs these changes are from (so it is easy to see what to include in the cv32e40s/dev to cv32e40x/dev merge)

#Variables:
date_time=$(date +%Y.%m.%d-%k.%M)


usage() {

  echo "usage: $0 --[s_into_x-dv|x-dv_into_s|sdev_into_xdev|xdev_into_sdev]"
  echo "--s_into_x-dv     Do a merge of core-v-verif cv32e40s/dev cv32e40s directory into cv32e40x-dv main (make sure the clonetb script has run)"
  echo "--x-dv_into_s     Do a merge of cv32e40x-dv main into core-v-verif cv32e40s/dev cv32e40s (not yet developed)"
  echo "--sdev_into_xdev  Do a merge of core-v-verif cv32e40s/dev into core-v-verif cv32e40x/dev"
  echo "--xdev_into_sdev  Do a merge of core-v-verif cv32e40x/dev into core-v-verif cv32e40s/dev"

  exit 1
}


merge_cv32e40s_into_cv32e40x-dv () {

  echo $'\n======= Merge of cv32e40s into cv32e40x-dv: =======\n'

  echo "=== Enter the cv32e40x-dv repo in cv32e40x subdirectory ==="
  cd cv32e40x

  echo "=== Make a branch in cv32e40x-dv that contain core-v-verif's cv32e40s folder from the cv32e40s/dev branch ==="
  git remote add ohw_cvv git@github.com:openhwgroup/core-v-verif.git
  git fetch ohw_cvv
  git checkout -b cvv_$date_time ohw_cvv/cv32e40s/dev
  git subtree split --prefix cv32e40s -b cv32e40s_$date_time

  echo "=== Make a branch based on the latest cv32e40x-dv content ==="
  git remote add ohw_x-dv git@github.com:openhwgroup/cv32e40x-dv.git
  git fetch ohw_x-dv
  git checkout -b merge_cv32e40s_$date_time ohw_x-dv/main

  echo "=== Merge ==="
  git merge -X find-renames --no-ff --no-commit cv32e40s_$date_time

}


move_files_40s_into_40x () {

  echo "=== Exchange 40x/X with 40s/S in file names ==="

  find . -type d | egrep -iv '\/\.|40sx|40xs' | grep -i 40s | xargs -n1 dirname | awk '{gsub(/40s/, "40x"); gsub(/40S/, "40X"); print}' | xargs -n2 mkdir -p
  find . -type d | egrep -iv '\/\.|40sx|40xs' | grep -i 40s | awk '{printf $1; printf " "; gsub(/40s/, "40x"); gsub(/40S/, "40X"); print}' | xargs -n2 git mv
  find . -type f | egrep -iv '\/\.|40sx|40xs' | grep -i 40s | xargs -n1 dirname | awk '{gsub(/40s/, "40x"); gsub(/40S/, "40X"); print}' | xargs -n2 mkdir -p
  find . -type f | egrep -iv '\/\.|40sx|40xs' | grep -i 40s | awk '{printf $1; printf " "; gsub(/40s/, "40x"); gsub(/40S/, "40X"); print}' | xargs -n2 git mv

}


substitute_file_content_40s_into_40x () {

  echo "=== Exchange 40x/X with 40s/S in file content ==="

  find . -type f -exec grep -Il . {} + | egrep -iv '\/\.|40sx|40xs' | xargs -n1 sed -i 's/40s/40x/g'
  find . -type f -exec grep -Il . {} + | egrep -iv '\/\.|40sx|40xs' | xargs -n1 sed -i 's/40S/40X/g'

}


merge_sdev_into_xdev () {

  echo $'\n======= Merge of core-v-verif cv32e40s/dev into cv32e40x/dev =======\n'

  echo "=== Download open hardware fork ==="
  git remote add ohw_cvv git@github.com:openhwgroup/core-v-verif.git
  git fetch ohw_cvv

  echo "=== Make a core-v-verif/cv32e40s/dev branch ==="
  git checkout -b cvv_sdev_$date_time ohw_cvv/cv32e40s/dev

  echo "=== Make a core-v-verif/cv32e40x/dev branch ==="
  git checkout -b cvv_xdev_$date_time ohw_cvv/cv32e40x/dev

  echo "=== Merge ==="
  git merge --no-commit --no-ff cvv_sdev_$date_time

}


merge_xdev_into_sdev () {

  echo $'\n======= Merge of core-v-verif cv32e40x/dev into cv32e40s/dev =======\n'

  echo "=== Download open hardware fork ==="
  git remote add ohw_cvv git@github.com:openhwgroup/core-v-verif.git
  git fetch ohw_cvv

  echo "=== Make a core-v-verif/cv32e40s/dev branch ==="
  git checkout -b cvv_xdev_$date_time ohw_cvv/cv32e40x/dev

  echo "=== Make a core-v-verif/cv32e40s/dev branch ==="
  git checkout -b cvv_sdev_$date_time ohw_cvv/cv32e40s/dev

  echo "=== Merge ==="
  git merge --no-commit --no-ff cvv_xdev_$date_time

}


check_cv32e40x_repo() {

  echo "=== Check if cv32e40x exist ==="
  if [ ! -d "cv32e40x" ]
  then
    echo "Directory cv32e40x does not exists."
    echo "Run: ./bin/clonetb -x"
    echo "before running: ./bin/merge_script --s_into_x-dv"
    exit 1
  fi

  echo "=== check if cv32e40x is the core-v-verif repo ==="
  cd cv32e40x

  if [ $(git config -l | grep remote.origin.url | grep core-v-verif) ]
  then
    echo "Directory cv32e40x is a core-v-verif repo and not a cv32e40x-dv repo."
    echo "Run: ./bin/clonetb -x"
    echo "before running: ./bin/merge_script --s_into_x-dv"
    exit 1
  fi

  cd ..

}


check_merge_status() {
  git status
}


main() {
  case $1 in
    "--s_into_x-dv")
      check_cv32e40x_repo
      merge_cv32e40s_into_cv32e40x-dv
      move_files_40s_into_40x
      substitute_file_content_40s_into_40x
      check_merge_status
      ;;
    "--x-dv_into_s")
      echo "This merge method is not yet developed"
      ;;
    "--sdev_into_xdev")
      merge_sdev_into_xdev
      check_merge_status
      ;;
    "--xdev_into_sdev")
      merge_xdev_into_sdev
      check_merge_status
      ;;
    *)
      usage
      ;;
  esac
}

main "$@"

