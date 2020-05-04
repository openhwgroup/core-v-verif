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

# riscv-dv env variables
export RISCV_TOOLCHAIN=$RISCV
export RISCV_GCC="$RISCV_TOOLCHAIN/bin/riscv64-unknown-elf-gcc"
export RISCV_OBJCOPY="$RISCV_TOOLCHAIN/bin/riscv64-unknown-elf-objcopy"
export SPIKE_PATH=$SPIKE_ROOT/bin
export RTL_PATH=$ROOT_PROJECT/cv64
export TESTS_PATH=$ROOT_PROJECT/tests

if ! [ -n "$DV_REPO" ]; then
  export DV_REPO="https://github.com/google/riscv-dv.git"
  export DV_BRANCH="master"
  export DV_HASH="0ce85d3187689855cd2b3b9e3fae21ca32de2248"
fi
echo $DV_REPO
echo $DV_BRANCH
echo $DV_HASH

mkdir -p uvm
if ! [ -e uvm/riscv-dv ]; then
  git clone $DV_REPO -b $DV_BRANCH uvm/riscv-dv
  cd uvm/riscv-dv; git checkout $DV_HASH; git apply ../../ci/riscv-dv.patch; cd -
fi

# install riscv-dv dependencies
cd uvm/riscv-dv; pip3 install --user -e .; cd -
