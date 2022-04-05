/*
 * Copyright (c) 2005-2022 Imperas Software Ltd., www.imperas.com
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
 * either express or implied.
 *
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 */

`ifndef INCLUDE_RVVI_SVH
`define INCLUDE_RVVI_SVH

`define RVVI_API_VERSION 12
`define RVVI_TRUE 1
`define RVVI_FALSE 0
`define RVVI_INVALID_INDEX -1

import "DPI-C" function int rvviVersionCheck(
    input int version);

import "DPI-C" function int rvviRefInit(
    input string programPath,
    input string vendor,
    input string variant,
    input int addressBusWidth,
    input int asyncDV);

import "DPI-C" function int rvviRefPcSet(
    input int hartId,
    input longint address);

import "DPI-C" function int rvviRefShutdown(
    );

import "DPI-C" function int rvviRefCsrSetVolatile(
    input int hartId,
    input int csrIndex);

import "DPI-C" function int rvviRefMemorySetVolatile(
    input longint addressLow,
    input longint addressHigh);

import "DPI-C" function longint rvviRefNetIndexGet(
    input string name);

import "DPI-C" function void rvviDutFprSet(
    input int hartId,
    input int fprIndex,
    input longint value);

import "DPI-C" function void rvviDutGprSet(
    input int hartId,
    input int gprIndex,
    input longint value);

import "DPI-C" function void rvviDutCsrSet(
    input int hartId,
    input int csrIndex,
    input longint value);

import "DPI-C" function void rvviRefNetSet(
    input longint netIndex,
    input longint value);

import "DPI-C" function void rvviDutRetire(
    input int hartId,
    input longint dutPc,
    input longint dutInsBin);

import "DPI-C" function void rvviDutTrap(
    input int hartId,
    input longint dutPc,
    input longint dutInsBin);

import "DPI-C" function int rvviRefEventStep(
    input int hartId);

import "DPI-C" function int rvviRefGprsCompare(
    input int hartId);

import "DPI-C" function int rvviRefGprsCompareWritten(
    input int hartId,
    input int ignoreX0);

import "DPI-C" function int rvviRefInsBinCompare(
    input int hartId);

import "DPI-C" function int rvviRefPcCompare(
    input int hartId);

import "DPI-C" function int rvviRefCsrCompare(
    input int hartId,
    input int csrIndex);

import "DPI-C" function void rvviRefCsrCompareEnable(
    input int hartId,
    input int csrIndex,
    input int enableState);

import "DPI-C" function int rvviRefCsrsCompare(
    input int hartId);

import "DPI-C" function int rvviRefVrsCompare(
    input int hartId);

import "DPI-C" function int rvviRefFprsCompare(
    input int hartId);

import "DPI-C" function longint rvviRefGprGet(
    input int hartId,
    input int index);

import "DPI-C" function int rvviRefGprsWrittenGet(
    input int hartId);

import "DPI-C" function longint rvviRefPcGet(
    input int hartId);

import "DPI-C" function longint rvviRefCsrGet(
    input int hartId,
    input int csrIndex);

import "DPI-C" function longint rvviRefInsBinGet(
    input int hartId);

import "DPI-C" function longint rvviRefFprGet(
    input int hartId,
    input int fprIndex);

import "DPI-C" function void rvviDutBusWrite(
    input int hartId,
    input longint address,
    input longint value,
    input longint byteEnableMask);

import "DPI-C" function void rvviRefMemoryWrite(
    input int hartId,
    input longint address,
    input longint data,
    input int size);

import "DPI-C" function longint rvviRefMemoryRead(
    input int hartId,
    input longint address,
    input int size);

import "DPI-C" function string rvviDasmInsBin(
    input int hartId,
    input longint insBin);

import "DPI-C" function string rvviRefCsrName(
    input int hartId,
    input int csrIndex);

import "DPI-C" function string rvviRefGprName(
    input int hartId,
    input int gprIndex);

import "DPI-C" function int rvviRefCsrPresent(
    input int hartId,
    input int csrIndex);

import "DPI-C" function int rvviRefFprsPresent(
    input int hartId);

`endif  // INCLUDE_RVVI_SVH
