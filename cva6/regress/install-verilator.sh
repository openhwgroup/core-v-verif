# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.fr)

set -e

if [ -z ${NUM_JOBS} ]; then
    NUM_JOBS=1
fi

if [ ! -f "$VERILATOR_ROOT/bin/verilator" ]; then
    echo "Installing Verilator"
    mkdir -p $VERILATOR_ROOT
    cd $VERILATOR_ROOT
    rm -f veriltor*.tgz 
    wget https://www.veripool.org/ftp/verilator-4.014.tgz
    tar xzf verilator*.tgz
    rm -f verilator*.tgz
    cd verilator-4.014
    mkdir -p $VERILATOR_ROOT
    # copy scripts
    autoconf && ./configure --prefix="$VERILATOR_ROOT" && make -j${NUM_JOBS}
    cp -r * $VERILATOR_ROOT/
    make test
else
    echo "Using Verilator from cached directory."
fi
