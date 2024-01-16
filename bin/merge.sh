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
your_cvv_branch=$(git rev-parse --abbrev-ref HEAD)


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
  read -p "y/n? [default: y] " yn

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
  read -p "y/n? [default: n] " yn
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

  echo "======= Cloning x-dv ======="

  read -p "This overwrites 'cv32e40x/'. Continue? y/n [default: y] " yn
  continue_check $yn

  ./bin/clonetb --x-main


}


check_merge_status() {

  git status

}


rejection_diff() {

  echo "======= Merging s/dev to x-dv, using 'theirs' ======="
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
  echo -e "\n======= Check if there are new commits i cv32e40s to merge to cv32e40x-dv ======="

  new_40s_commits=()
  num_40s_commits_to_check=100
  num_40x_commits_to_check=100

  # Get the updated commit messages from cv32e40s
  echo -e "\n== Checkout an updated cv32e40s/dev branch =="
  git remote add ohw_cvv git@github.com:openhwgroup/core-v-verif.git
  git fetch ohw_cvv
  git checkout ohw_cvv/cv32e40s/dev
  commit_messages_40s=$(git log --format=%s -$num_40s_commits_to_check -- cv32e40s)

  for commit_message in $commit_messages_40s; do

    # Check if the commit message exist in cv32e40x (checks only the <num_40x_commits_to_check> last commits of 40x)
    cd cv32e40x
    is_commit_message_in_40x=$(git log -$num_40x_commits_to_check --grep="$commit_message" --format=oneline)
    cd ..

    if [[ -z $is_commit_message_in_40x ]]; then
      # Add new 40s commit to list. Display the new item with sha and commit message
      new_40s_commit_wit_both_sha_and_message=$(git log -$num_40s_commits_to_check --grep="$commit_message" --format=oneline)
      new_40s_commits+=("$new_40s_commit_wit_both_sha_and_message")
    fi

  done

  echo -e "\n== Restore your cvv branch =="
  git checkout $your_cvv_branch

  # Print commits needed to be merged,
  if [[ -n $new_40s_commits ]]; then
    echo -e "\n== New commits in cv32e40s that need to be merged: =="
    for ((i=0; i <= ${#new_40s_commits[@]} ; i++)); do
      echo ${new_40s_commits[$i]}
    done

  else
    echo -e "\n== No new commits in cv32e40s that need to be merged =="
  fi

  # List warnings and ask to continue merge
  echo "== WARNING 1: =="
  echo "The script use commit message to identify merged commits"
  echo "If a new commit in cv32e40s has the same commit message as a commit in cv32e40x-dv or no -m at all,"
  echo -e "the commit is not in the list of commits that need to be merged.\n"

  echo "== WARNING 2: =="
  echo "The script compares only the 100 latest commits in cv32e40s and cv32e40x-dv"
  echo -e "If there has been a lot of activity in the reposetories, the result of the above check can be faulty.\n"

  read -p "Merge the commits into cv32e40x-dv? y/n [default: y] " yn
  continue_check $yn

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

recommended_way_forward() {
  echo "======= Recommended way forward ======="

  echo "1) Evaluate all git conflict"
  echo "2) Run git diff HEAD on all files (red and green files) to see all merge changes"
  echo "3) If some files are not renamed from 40s to 40x, the file content is too different to be recognized as the same file."
  echo "   Compare the 40s and 40x version of the same file and know there are new changes in the 40s version"
  echo "   that must manualy be merged to the 40x version. Delete the 40s version of the file after the manual merge is finished."

}

main() {
  case $1 in
    "--s_into_x-dv")
      clone_x_dv
      need_40s_40x-dv_merge
      merge_cv32e40s_into_cv32e40x-dv
      move_files_40s_into_40x
      substitute_file_content_40s_into_40x
      check_merge_status
      recommended_way_forward
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
