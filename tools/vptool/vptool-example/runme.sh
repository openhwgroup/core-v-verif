#!/bin/sh -v
#############################################################################
# Copyright (C) 2022 Thales DIS France SAS
#
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0.
#
# Original Author: Zbigniew Chamski (Thales)
#############################################################################

# Root of the example directories.  VPTOOL wrapper 'vptool.sh'
# is located in parent dir of 'vptool-example.sh'.
ROOTDIR=`readlink -f $(dirname $0)`

# Set up platform location.  It can be anywhere but should contain
# a valid `vp_config.py` file in `vptool` directory.
# Here we use a structured verification tree from the example directory.
export PLATFORM_TOP_DIR="$ROOTDIR/example-database/ip_dir/core-v/cva6/"

# Let the user know about the env variable settings.
echo 'export PLATFORM_TOP_DIR="$PLATFORM_TOP_DIR"'

# Set a meaningful name for the example project.
export PROJECT_NAME="VPTOOL example project"
echo 'export PROJECT_NAME="VPTOOL example project"'

# Set an alphanumerical identifier for the example project.
# It should follow C/Python naming tules (in particular,
# use only characters in set [0-9_A-Za-z].)
export PROJECT_IDENT="VPTOOL_example"
echo 'export PROJECT_IDENT="VPTOOL_example"'

# Run VPTOOL overriding the default theme with 'winxpblue',
# and pass all user args (possibly yet another theme spec!)
echo "sh $ROOTDIR/../vptool.sh -t winxpblue $*"
sh $ROOTDIR/../vptool.sh -t winxpblue $*
