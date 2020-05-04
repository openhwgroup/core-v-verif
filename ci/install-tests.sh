###############################################################################
#
# Copyright 2020 Thales
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
###############################################################################
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@invia.fr)
#
###############################################################################

if ! [ -n "$TESTS_REPO" ]; then
  TESTS_REPO="https://github.com/riscv/riscv-compliance.git"
  TESTS_BRANCH="master"
  TESTS_HASH="220e78542da4510e40eac31e31fdd4e77cdae437"
fi
echo $TESTS_REPO
echo $TESTS_BRANCH
echo $TESTS_HASH

mkdir -p tests
if ! [ -e tests/riscv-compliance ]; then
  git clone $TESTS_REPO -b $TESTS_BRANCH tests/riscv-compliance
  cd tests/riscv-compliance; git checkout $TESTS_HASH; git apply ../../ci/riscv-compliance.patch; cd -
fi
