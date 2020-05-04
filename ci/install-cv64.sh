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

# Customise this to a fast local disk
export ROOT_PROJECT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../" && pwd)
export TOP=$ROOT_PROJECT/tools

# where to install the tools
if ! [ -n "$RISCV" ]; then
  echo "Error: RISCV variable undefined"
  return
fi

# install Verilator 
if ! [ -n "$VERILATOR_ROOT" ]; then
  export VERILATOR_ROOT=$TOP/verilator-4.014/
fi
ci/install-verilator.sh

export PATH=$RISCV/bin:$VERILATOR_ROOT/bin:$PATH
export LIBRARY_PATH=$RISCV/lib
export LD_LIBRARY_PATH=$RISCV/lib
export C_INCLUDE_PATH=$RISCV/include:$VERILATOR_ROOT/include
export CPLUS_INCLUDE_PATH=$RISCV/include:$VERILATOR_ROOT/include

# number of parallel jobs to use for make commands and simulation
export NUM_JOBS=24

# install the required tools for cv64
if ! [ -n "$CV64_REPO" ]; then
  CV64_REPO="https://github.com/pulp-platform/ariane.git"
  CV64_BRANCH="master"
  CV64_HASH="1793be633e096bacbbef7fc75fbe5b35da59c91b"
fi
echo $CV64_REPO
echo $CV64_BRANCH
echo $CV64_HASH

if ! [ -e cv64 ]; then
  git clone --recursive $CV64_REPO -b $CV64_BRANCH cv64
  cd cv64; git checkout $CV64_HASH; git apply ../ci/cv64.patch; cd -
fi

# install Spike
export SPIKE_ROOT=$TOP/spike/
ci/install-spike.sh
