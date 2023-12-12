###############################################################################
# Variables to determine the the command to clone external repositories.
# For each repo there are a set of variables:
#      *_REPO:   URL to the repository in GitHub.
#      *_BRANCH: Name of the branch you wish to clone;
#                Set to 'master' to pull the master branch.
#      *_HASH:   Value of the specific hash you wish to clone;
#                Set to 'head' to pull the head of the branch you want.
# THe CV32E40S repo also has a variable to clone a specific tag:
#      *_TAG:    Value of the specific tag you wish to clone;
#                Will override the HASH unless set to "none".
#

export SHELL = /bin/bash

CV_CORE_REPO   ?= https://github.com/openhwgroup/cv32e40s
CV_CORE_BRANCH ?= master
CV_CORE_HASH   ?= 04947655f5642821f78904f8feb13dd677fbcc6d
CV_CORE_TAG    ?= none

#RISCVDV_REPO    ?= https://github.com/google/riscv-dv
RISCVDV_REPO    ?= https://github.com/silabs-hfegran/riscv-dv
#RISCVDV_BRANCH  ?= master
RISCVDV_BRANCH  ?= dev_hf
#RISCVDV_HASH    ?= 797aa0762de8e2c8d427b978483b47dd7649954a
RISCVDV_HASH    ?= 13e0cdf5d50e882d939e9a0d0afe093ee1c68290

EMBENCH_REPO    ?= https://github.com/embench/embench-iot.git
EMBENCH_BRANCH  ?= master
EMBENCH_HASH    ?= 6934ddd1ff445245ee032d4258fdeb9828b72af4

# TODO: silabs-hfegran: Temporary fork compliance suite to support bitmanip and
# new repository structure. Revert back to latest mainline when bitmanip PR has
# been approved and local changes upstreamed.
# 2022-02-21
COMPLIANCE_REPO   ?= https://github.com/silabs-hfegran/riscv-arch-test.git
COMPLIANCE_BRANCH ?= dev_hf_riscv_arch_test
COMPLIANCE_HASH   ?= 43556e3ae4e98d5e739204f37a11769e14154b7e

# This Spike repo is only cloned when the DPI disassembler needs to be rebuilt
# Typically users can simply use the checked-in shared library
DPI_DASM_SPIKE_REPO   ?= https://github.com/riscv/riscv-isa-sim.git
DPI_DASM_SPIKE_BRANCH ?= master
DPI_DASM_SPIKE_HASH   ?= 8faa928819fb551325e76b463fc0c978e22f5be3

# SVLIB
SVLIB_REPO       ?= https://bitbucket.org/verilab/svlib/src/master/svlib
SVLIB_BRANCH     ?= master
SVLIB_HASH       ?= c25509a7e54a880fe8f58f3daa2f891d6ecf6428
