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

#pragma once

/*! \file rvvi-api.h
 *  \brief RVVI interface, C API header.
**/

#include <stdint.h>

typedef uint32_t bool_t;

#define RVVI_API_VERSION 12
#define RVVI_TRUE 1
#define RVVI_FALSE 0
#define RVVI_INVALID_INDEX -1

#ifdef __cplusplus
extern "C" {
#endif

/*! \brief Check the compiled RVVI API version.
 *
 *  Makes sure the ImperasDV version linked with matches the versions defined in this header file. This should be called before any other RVVI API function.  If this function returns RVVI_FALSE, no other RVVI API function should be called.
 *
 *  \param version Should be set to RVVI_API_VERSION.
 *
 *  \return RVVI_TRUE if versions matches otherwise RVVI_FALSE.
**/
extern bool_t rvviVersionCheck(
    uint32_t version);

/*! \brief Initialize the DV reference model.
 *
 *  \param programPath File path of the ELF file to be executed. This parameter can be NULL if required.
 *  \param vendor Vendor string that the reference model will use.
 *  \param variant Variant string that the reference model will use.
 *  \param addressBusWidth The width in bits of the processors address bus. Set to 0 to use the maximum available width.
 *  \param asyncDV Set to RVVI_TRUE to enable asynchronous DV support.
 *
 *  \return RVVI_TRUE if the reference was initialized successfully else RVVI_FALSE.
 *
 *  \note The reference model will begin execution from the entry point of the provided ELF file but can be overridden by the rvviRefPcSet() function.
**/
extern bool_t rvviRefInit(
    const char *programPath,
    const char *vendor,
    const char *variant,
    uint32_t addressBusWidth,
    bool_t asyncDV);

/*! \brief Force the PC of the reference model to be particular value.
 *
 *  \param hartId The hart to change the PC register of.
 *  \param address The address to change the PC register to.
 *
 *  \return RVVI_TRUE on success else RVVI_FALSE.
**/
extern bool_t rvviRefPcSet(
    uint32_t hartId,
    uint64_t address);

/*! \brief Shutdown the reference module releasing any used resources.
 *
 *
 *  \return Returns RVVI_TRUE if shutdown was successful else RVVI_FALSE.
**/
extern bool_t rvviRefShutdown(
    void);

/*! \brief Notify the reference that a CSR is considered volatile.
 *
 *  \param hartId The hart that has updated its GPR.
 *  \param csrIndex Index of the CSR register to be considered volatile (0x0 to 0xfff).
 *
 *  \return Returns RVVI_TRUE if operation was successful else RVVI_FALSE.
**/
extern bool_t rvviRefCsrSetVolatile(
    uint32_t hartId,
    uint32_t csrIndex);

/*! \brief Notify the reference that a memory region is volatile.
 *
 *  \param addressLow Lower address of the volatile memory region
 *  \param addressHigh Upper address of the volatile memory region (inclusive)
 *
 *  \return Returns RVVI_TRUE if operation was successful else RVVI_FALSE.
**/
extern bool_t rvviRefMemorySetVolatile(
    uint64_t addressLow,
    uint64_t addressHigh);

/*! \brief Lookup a net on the reference model and return its index.
 *
 *  \param name The net name to locate.
 *
 *  \return Unique index for this net or RVVI_INVALID_INDEX if it was not found.
 *
 *  \note Please consult the model datasheet for a list of valid net names.
 *  \note See also, rvviRefNetSet().
**/
extern uint64_t rvviRefNetIndexGet(
    const char *name);

/*! \brief Notify RVVI that a DUT RVV Vector register has been written to.
 *
 *  \param hartId The hart that has updated its FPR.
 *  \param vrIndex The FPR index within the register file (0 to 31).
 *  \param data Memory to copy the vector register from.
 *  \param size Size of the memory buffer data parameter in bytes.
**/
extern void rvviDutVrSet(
    uint32_t hartId,
    uint32_t vrIndex,
    void *data,
    uint32_t size);

/*! \brief Notify RVVI that a DUT floating point register has been written to.
 *
 *  \param hartId The hart that has updated its FPR.
 *  \param fprIndex The FPR index within the register file (0 to 31).
 *  \param value The value that has been written.
**/
extern void rvviDutFprSet(
    uint32_t hartId,
    uint32_t fprIndex,
    uint64_t value);

/*! \brief Notify RVVI that a DUT GPR has been written to.
 *
 *  \param hartId The hart that has updated its GPR.
 *  \param gprIndex The GPR index within the register file.
 *  \param value The value that has been written.
**/
extern void rvviDutGprSet(
    uint32_t hartId,
    uint32_t gprIndex,
    uint64_t value);

/*! \brief Notify RVVI that a DUT CSR has been written to.
 *
 *  \param hartId The hart that has updated its CSR.
 *  \param csrIndex The CSR index (0x0 to 0xfff).
 *  \param value The value that has been written.
**/
extern void rvviDutCsrSet(
    uint32_t hartId,
    uint32_t csrIndex,
    uint64_t value);

/*! \brief Propagate a net change to the reference model.
 *
 *  \param netIndex The net index returned prior by rvviRefNetIndexGet().
 *  \param value The new value to set the net state to.
**/
extern void rvviRefNetSet(
    uint64_t netIndex,
    uint64_t value);

/*! \brief Notify the reference that a DUT instruction has retired.
 *
 *  \param hartId The hart that has retired an instruction.
 *  \param dutPc The address of the instruction that has retired.
 *  \param dutInsBin The binary instruction representation.
**/
extern void rvviDutRetire(
    uint32_t hartId,
    uint64_t dutPc,
    uint64_t dutInsBin);

/*! \brief Notify the reference that the DUT received a trap.
 *
 *  \param hartId The hart that has retired an instruction.
 *  \param dutPc The address of the instruction that has retired.
 *  \param dutInsBin The binary instruction representation.
**/
extern void rvviDutTrap(
    uint32_t hartId,
    uint64_t dutPc,
    uint64_t dutInsBin);

/*! \brief Step the reference model until the next event.
 *
 *  \param hartId The ID of the hart that is being stepped.
 *
 *  \return Returns RVVI_TRUE if the step was successful else RVVI_FALSE.
**/
extern bool_t rvviRefEventStep(
    uint32_t hartId);

/*! \brief Compare all GPR register values between reference and DUT.
 *
 *  \param hartId The ID of the hart that is being compared.
 *
 *  \return RVVI_FALSE if there are any mismatches, otherwise RVVI_TRUE.
**/
extern bool_t rvviRefGprsCompare(
    uint32_t hartId);

/*! \brief Compare GPR registers that have been written to between the reference and DUT. This can be seen as a super set of the rvviRefGprsCompare function. This comparator will also flag differences in the set of registers that have been written to.
 *
 *  \param hartId The ID of the hart that is being compared.
 *  \param ignoreX0 RVVI_TRUE to not compare writes to the x0 register, which may be treated as a special case, otherwise RVVI_FALSE.
 *
 *  \return RVVI_FALSE if there are any mismatches, otherwise RVVI_TRUE.
**/
extern bool_t rvviRefGprsCompareWritten(
    uint32_t hartId,
    bool_t ignoreX0);

/*! \brief Compare retired instruction bytes between reference and DUT.
 *
 *  \param hartId The ID of the hart that is being compared.
 *
 *  \return RVVI_FALSE if there are any mismatches, otherwise RVVI_TRUE.
**/
extern bool_t rvviRefInsBinCompare(
    uint32_t hartId);

/*! \brief Compare program counter for the retired instructions between DUT and the the reference model.
 *
 *  \param hartId The ID of the hart that is being compared.
 *
 *  \return RVVI_FALSE if there are any mismatches, otherwise RVVI_TRUE.
**/
extern bool_t rvviRefPcCompare(
    uint32_t hartId);

/*! \brief Compare a CSR value between DUT and the the reference model.
 *
 *  \param hartId The ID of the hart that is being compared.
 *  \param csrIndex The index of the CSR register being compared.
 *
 *  \return RVVI_FALSE if there are any mismatches, otherwise RVVI_TRUE.
**/
extern bool_t rvviRefCsrCompare(
    uint32_t hartId,
    uint32_t csrIndex);

/*! \brief Enable or disable comparison of a specific CSR during rvviRefCsrsCompare.
 *
 *  \param hartId The ID of the hart that this should apply to.
 *  \param csrIndex The index of the CSR to enable or disable comparison of.
 *  \param enableState RVVI_TRUE to enable comparison or RVVI_FALSE to disable.
**/
extern void rvviRefCsrCompareEnable(
    uint32_t hartId,
    uint32_t csrIndex,
    bool_t enableState);

/*! \brief Compare all CSR values between DUT and the the reference model.
 *
 *  This function will compare the value of all CSRs between the reference and the DUT. Note that specific CSRs can be removed from this comparison by using the rvviRefCsrCompareEnable function.
 *
 *  \param hartId The ID of the hart that is being compared.
 *
 *  \return RVVI_FALSE if there are any mismatches, otherwise RVVI_TRUE.
**/
extern bool_t rvviRefCsrsCompare(
    uint32_t hartId);

/*! \brief Compare all RVV vector register values between reference and DUT.
 *
 *  \param hartId The ID of the hart that is being compared.
 *
 *  \return RVVI_FALSE if there are any mismatches, otherwise RVVI_TRUE.
**/
extern bool_t rvviRefVrsCompare(
    uint32_t hartId);

/*! \brief Compare all floating point register values between reference and DUT.
 *
 *  \param hartId The ID of the hart that is being compared.
 *
 *  \return RVVI_FALSE if there are any mismatches, otherwise RVVI_TRUE.
**/
extern bool_t rvviRefFprsCompare(
    uint32_t hartId);

/*! \brief Read a GPR value from a hart in the reference model.
 *
 *  \param hartId The hart to retrieve the GPR from.
 *  \param index Index of the GPR register to read.
 *
 *  \return GPR value read from the reference model.
**/
extern uint64_t rvviRefGprGet(
    uint32_t hartId,
    uint32_t index);

/*! \brief Read a GPR written mask from the last rvviRefEventStep.
 *
 *  Each bit index in the mask returned indicates if the corresponding GPR has been written to by the reference model. Ie, if bit 3 is set, then X3 was written to.
 *
 *  \param hartId The hart to retrieve the GPR written mask from.
 *
 *  \return The GPR written mask.
**/
extern uint32_t rvviRefGprsWrittenGet(
    uint32_t hartId);

/*! \brief Return the program counter of a hart in the reference model.
 *
 *  \param hartId The hart to retrieve the PC from.
 *
 *  \return The program counter of the specified hart.
**/
extern uint64_t rvviRefPcGet(
    uint32_t hartId);

/*! \brief Read a CSR value from a hart in the reference model.
 *
 *  \param hartId The hart to retrieve the CSR from.
 *  \param csrIndex Index of the CSR register to read (0x0 to 0xfff).
 *
 *  \return The CSR register value read from the specified hart.
**/
extern uint64_t rvviRefCsrGet(
    uint32_t hartId,
    uint32_t csrIndex);

/*! \brief Return the binary representation of the previously retired instruction.
 *
 *  \param hartId The hart to retrieve the instruction from.
 *
 *  \return The instruction bytes.
**/
extern uint64_t rvviRefInsBinGet(
    uint32_t hartId);

/*! \brief Read a floating point register value from a hart in the reference model.
 *
 *  \param hartId The hart to retrieve the FPR register from.
 *  \param fprIndex Index of the floating point register to read.
 *
 *  \return The FPR register value read from the specified hart.
**/
extern uint64_t rvviRefFprGet(
    uint32_t hartId,
    uint32_t fprIndex);

/*! \brief Read a RVV vector register value from a hart in the reference model.
 *
 *  \param hartId The hart to retrieve the vector register from.
 *  \param vrIndex Index of the vector register to read.
 *  \param data Pointer to memory that the vector regsiter will be written to.
 *  \param size Size of the memory region pointed to by data.
**/
extern void rvviRefVrGet(
    uint32_t hartId,
    uint32_t vrIndex,
    void *data,
    uint32_t size);

/*! \brief Notify RVVI that the DUT has been written to memory.
 *
 *  \param hartId The hart that issued the data bus write.
 *  \param address The address the hart is writing to.
 *  \param value The value placed on the data bus.
 *  \param byteEnableMask The byte enable mask provided for this write.
 *
 *  \note Bus writes larger than 64bits should be reported using multiple calls to this function.
 *  \note byteEnableMask bit 0 corresponds to address+0, bEnMask bit 1 corresponds to address+1, etc.
**/
extern void rvviDutBusWrite(
    uint32_t hartId,
    uint64_t address,
    uint64_t value,
    uint64_t byteEnableMask);

/*! \brief Write data to the reference models physical memory space.
 *
 *  \param hartId The hart to write from the perspective of.
 *  \param address The address being written to.
 *  \param data The data byte being written into memory.
 *  \param size Size of the data being written in bytes (1 to 8).
**/
extern void rvviRefMemoryWrite(
    uint32_t hartId,
    uint64_t address,
    uint64_t data,
    uint32_t size);

/*! \brief Read data from the reference models physical memory space.
 *
 *  \param hartId The hart to read from the perspective of.
 *  \param address The address being read from.
 *  \param size Size of the data being read in bytes (1 to 8).
 *
 *  \return The data that has been read from reference memory.
**/
extern uint64_t rvviRefMemoryRead(
    uint32_t hartId,
    uint64_t address,
    uint32_t size);

/*! \brief Disassemble an arbitrary instruction encoding.
 *
 *  \param hartId Hart with the ISA we are disassembling for.
 *  \param insBin The raw instruction that should be disassembled.
 *
 *  \return Null terminated string containing the disassembly.
**/
extern const char *rvviDasmInsBin(
    uint32_t hartId,
    uint64_t insBin);

/*! \brief Return the name of a CSR in the reference model.
 *
 *  \param hartId Hart with the CSR we are looking up the name of.
 *  \param csrIndex The index of the CSR we are looking up (0x0 to 0xfff inclusive).
 *
 *  \return Null terminated string containing the CSR name.
**/
extern const char *rvviRefCsrName(
    uint32_t hartId,
    uint32_t csrIndex);

/*! \brief Return the ABI name of a GPR in the reference model.
 *
 *  \param hartId Hart with the GPR we are looking up the name of.
 *  \param gprIndex The index of the GPR we are looking up (0 to 31 inclusive).
 *
 *  \return Null terminated string containing the GPR ABI name.
**/
extern const char *rvviRefGprName(
    uint32_t hartId,
    uint32_t gprIndex);

/*! \brief Check if a CSR is present in the reference model.
 *
 *  \param hartId Hart with the CSR we are checking the presence of.
 *  \param csrIndex The index of the CSR we are checking for (0x0 to 0xfff inclusive).
 *
 *  \return RVVI_TRUE if the CSR is present in the reference model else RVVI_FALSE.
**/
extern bool_t rvviRefCsrPresent(
    uint32_t hartId,
    uint32_t csrIndex);

/*! \brief Check if FPR registers are present in the reference model.
 *
 *  \param hartId Hart with the FPR we are checking the presence of.
 *
 *  \return RVVI_TRUE if the FPR is present in the reference model else RVVI_FALSE.
**/
extern bool_t rvviRefFprsPresent(
    uint32_t hartId);

#ifdef __cplusplus
}  // extern "C"
#endif
