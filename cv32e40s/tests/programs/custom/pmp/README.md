<!-- Copyright 2022 OpenHW Group
Copyright 2022 Silicon Labs, Inc.

Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://solderpad.org/licenses/

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

SPDX-License-Identifier:Apache-2.0 WITH SHL-2.0 -->

This folder includes the direct tests covering the default PMP behavior when PMP_NUM_REGIONS=64.

All tests are enabled by default and individually test can be enabled or disabled by commenting the test function in `main()` in `pmp.c`.

At this stage, when testing `tor_zero()` the ISS should be disabled `USE_ISS=0` due to some mismatch issue.