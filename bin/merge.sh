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


#Variables:
date_time=$(date +%Y.%m.%d-%H.%M)


usage() {

  echo "usage: $0 --[s_into_x-dv|sdev_into_xdev|xdev_into_sdev|rejection-diff]"
  echo "--s_into_x-dv     Do a merge of core-v-verif cv32e40s/dev cv32e40s directory into cv32e40x-dv main (make sure the clonetb script has run)"
  echo "--sdev_into_xdev  Do a merge of core-v-verif cv32e40s/dev into core-v-verif cv32e40x/dev"
  echo "--xdev_into_sdev  Do a merge of core-v-verif cv32e40x/dev into core-v-verif cv32e40s/dev"
  echo "--rejection-diff  Merge s/dev to x-dv, using 'theirs'"

  exit 1

}


die() {

  scriptname=$0
  message=$1
  echo "$scriptname: error: $message"
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

  echo "======= Replace 40s/S with 40x/X in file names? (recommended) ======="
  read -p "(default: y, n)?" yn

  case $yn in
    [Nn])
      echo "=== Skip file renaming ===";
      return
      ;;

    *)
    echo "=== Rename files ==="
      find . -type d | egrep -iv '\/\.|40sx|40xs' | grep -i 40s | xargs -n1 dirname | awk '{gsub(/40s/, "40x"); gsub(/40S/, "40X"); print}' | xargs -n2 mkdir -p
      find . -type d | egrep -iv '\/\.|40sx|40xs' | grep -i 40s | awk '{printf $1; printf " "; gsub(/40s/, "40x"); gsub(/40S/, "40X"); print}' | xargs -n2 git mv -f
      find . -type f | egrep -iv '\/\.|40sx|40xs' | grep -i 40s | xargs -n1 dirname | awk '{gsub(/40s/, "40x"); gsub(/40S/, "40X"); print}' | xargs -n2 mkdir -p
      find . -type f | egrep -iv '\/\.|40sx|40xs' | grep -i 40s | awk '{printf $1; printf " "; gsub(/40s/, "40x"); gsub(/40S/, "40X"); print}' | xargs -n2 git mv -f

      ;;
  esac
}


substitute_file_content_40s_into_40x () {

  echo "======= Exchange 40x/X with 40s/S in file content? (not recommended) ======="
  read -p "(y, default: n)?" yn
  case $yn in
    [Yy])
      echo "=== Content substitution ===";

      find . -type f -exec grep -Il . {} + | egrep -iv '\/\.|40sx|40xs' | xargs -n1 sed -i 's/40s/40x/g'
      find . -type f -exec grep -Il . {} + | egrep -iv '\/\.|40sx|40xs' | xargs -n1 sed -i 's/40S/40X/g'

      return
      ;;

    *)
      echo "=== Skip content substitution ===";
      ;;
  esac

}


merge_sdev_into_xdev () {

  echo $'\n======= Merge of core-v-verif cv32e40s/dev into cv32e40x/dev =======\n'

  echo "=== Download open hardware fork ==="
  git remote add ohw_cvv git@github.com:openhwgroup/core-v-verif.git
  git fetch ohw_cvv

  echo "=== Make a core-v-verif/cv32e40s/dev branch ==="
  git checkout -b cvv_sdev_$date_time ohw_cvv/cv32e40s/dev


  echo "=== Make a core-v-verif/cv32e40x/dev branch ==="
  git checkout -b merge_sdev_into_xdev_$date_time ohw_cvv/cv32e40x/dev


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
  git checkout -b merge_xdev_into_sdev_$date_time ohw_cvv/cv32e40s/dev


  echo "=== Merge ==="
  git merge --no-commit --no-ff cvv_xdev_$date_time


}


clone_x_dv() {

  echo "=== Cloning x-dv ==="

  read -p "This overwrites 'cv32e40x/'. Continue? (default: y, n) " yn
  continue_check $yn

  ./bin/clonetb --x-main


}


check_merge_status() {

  git status

}


rejection_diff() {

  echo "=== Merging s/dev to x-dv, using 'theirs' ==="
  echo "WARNING, this function is crude and makes assumptions."

  cd cv32e40x
  branch_name_40s_subtree=$(git branch | grep ' cv32e40s')
  branch_name_merge_normal=$(git branch | grep 'merge')
  branch_name_merge_theirs=$(echo $branch_name_merge_normal | sed 's/merge/theirs/')

  git checkout main  ||  die "can't checkout main"
  git checkout -B $branch_name_merge_theirs  ||  die "can't create branch"
  git merge -X theirs $branch_name_40s_subtree

  move_files_40s_into_40x
  substitute_file_content_40s_into_40x

}

need_40s_40x-dv_merge(){
  echo -e "\n=== Check if there are new commits i cv32e40s to merge to cv32e40x-dv ==="

  missing_commits=()
  nr_commits=10
  nr_commits_to_check=10

  # Get commit shas from cv32e40s:
  cv32e40s_commits_shas=$(git log --pretty=format:'%H' -$nr_commits -- cv32e40s)
  for sha in $cv32e40s_commits_shas; do
    commit_message=$(git show -s --format=%s%b $sha)

    # If the commit is signed off search for the commit's -m message in cv32e40x-dv
    # to check if the commit is merged or not.
    if [[ $commit_message  =~ "Signed-off-by" ]]; then
      commit_m_message=${commit_message%Signed-off-by*}

      cd cv32e40x
      search_commit=$(git log -$nr_commits_to_check --grep="$commit_m_message" --format=oneline)
      cd ..

      if [[ -z $search_commit ]]; then
        missing_commit="$sha: $commit_message"
        missing_commits+=("$missing_commit")
      fi
    fi
  done

  # Print commits needed to be merged,
  if [[ -n $missing_commits ]]; then
    echo -e "\n== Commits needed to be merged: =="
    echo "There is a chance more commits need merge"
    echo "The commits with similar name to another commit in cv32e40x-dv is not listed"
    for ((i=0; i <= ${#missing_commits[@]} ; i++)); do
      echo ${missing_commits[$i]}
    done

  else
    echo -e "\n== No commits needs to be merged =="
    echo "(Unless there is a commit without -m message that needs to be merged)"
  fi

  # Ask to continue merge
  read -p "Merge commits into cv32e40x-dv? (default: y, n) " yn
  continue_check $yn

}

get_branch_cv32e40s_dev() {

  echo -e "\n== Enter an updated cv32e40s/dev branch =="
  git remote add ohw_cvv git@github.com:openhwgroup/core-v-verif.git
  git fetch ohw_cvv
  git checkout ohw_cvv/cv32e40s/dev

}

continue_check() {
  case $1 in
    [Nn])
      echo "Exit merge!"
      exit 1
      ;;
    *)
      echo "Continue merge process!"
      return
      ;;
  esac
}


main() {
  case $1 in
    "--s_into_x-dv")
      clone_x_dv
      get_branch_cv32e40s_dev
      need_40s_40x-dv_merge
      merge_cv32e40s_into_cv32e40x-dv
      move_files_40s_into_40x
      substitute_file_content_40s_into_40x
      check_merge_status
      ;;
    "--sdev_into_xdev")
      merge_sdev_into_xdev
      check_merge_status
      ;;
    "--xdev_into_sdev")
      merge_xdev_into_sdev
      check_merge_status
      ;;
    "--rejection-diff")
      rejection_diff
      ;;
    *)
      usage
      ;;
  esac

}

main "$@"
