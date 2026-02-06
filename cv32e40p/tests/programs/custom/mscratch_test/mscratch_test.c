/*
**
** Copyright 2026 OpenHW Group
**
** Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
** you may not use this file except in compliance with the License.
** You may obtain a copy of the License at
**
**     https://solderpad.org/licenses/
**
** Unless required by applicable law or agreed to in writing, software
** distributed under the License is distributed on an "AS IS" BASIS,
** WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
** See the License for the specific language governing permissions and
** limitations under the License.
**
*****fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
**
** CSR Read/Write Test - Standalone, Self-Checking
**
** SCOPE: MSCRATCH (0x340) ONLY
**
** Why only MSCRATCH:
**   - Simple 32-bit fully R/W register with no masking or constraints
**   - Direct assignment: mscratch_n = csr_wdata_int;
**
** Other CSRs fail for these reasons:
**   DSCRATCH0/1 (0x7B2/0x7B3): Debug mode only (illegal instruction in normal mode)
**   MEPC (0x341): Bit 0 masked: mepc_n = csr_wdata_int & ~32'b1;
**   DEPC (0x7B1): Debug mode only + bit 0 masked
**   MSTATUS (0x300): Only specific bits R/W (uie, mie, upie, mpie, mpp, mprv)
**   MIE (0x304): Masked by IRQ: mie_n = csr_wdata_int & IRQ_MASK;
**   MTVEC (0x305): Only [31:8] and [0] used, [7:1] ignored
**
*****fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
*/

#include <stdint.h>


#define RESULT_REG  ((volatile uint32_t *)0x20000000) 
#define PASS_VALUE  123456789
#define FAIL_VALUE  1


#define CSR_READ(addr, dst) asm volatile("csrr %0, " #addr : "=r"(dst))
#define CSR_WRITE(addr, val) asm volatile("csrw " #addr ", %0" : : "r"(val))


#define CSR_WRITE_CHECK(addr, val, expect, errs) do {   \
    uint32_t _wr = (val);                               \
    uint32_t _ex = (expect);                            \
    uint32_t _rd;                                       \
    CSR_WRITE(addr, _wr);                               \
    CSR_READ(addr, _rd);                                \
    if (_rd != _ex) {                                   \
        (errs)++;                                       \
    }                                                   \
} while (0)


#define TEST_RESET_VALUE(addr, reset_val, errs) do {    \
    uint32_t _rd;                                       \
    CSR_READ(addr, _rd);                                \
    if (_rd != (uint32_t)(reset_val)) {                 \
        (errs)++;                                       \
    }                                                   \
} while (0)


#define TEST_BASIC_PATTERNS(addr, errs) do {                \
    CSR_WRITE_CHECK(addr, 0x00000000, 0x00000000, errs);    \
    CSR_WRITE_CHECK(addr, 0xFFFFFFFF, 0xFFFFFFFF, errs);    \
    CSR_WRITE_CHECK(addr, 0xAAAAAAAA, 0xAAAAAAAA, errs);    \
    CSR_WRITE_CHECK(addr, 0x55555555, 0x55555555, errs);    \
    CSR_WRITE_CHECK(addr, 0xA5A5A5A5, 0xA5A5A5A5, errs);    \
    CSR_WRITE_CHECK(addr, 0x5A5A5A5A, 0x5A5A5A5A, errs);    \
} while (0)


#define TEST_WALKING_ONES(addr, errs) do {          \
    for (int _i = 0; _i < 32; _i++) {               \
        uint32_t _pat = (uint32_t)1 << _i;          \
        CSR_WRITE_CHECK(addr, _pat, _pat, errs);    \
    }                                               \
} while (0)


#define TEST_WALKING_ZEROS(addr, errs) do {         \
    for (int _i = 0; _i < 32; _i++) {               \
        uint32_t _pat = ~((uint32_t)1 << _i);       \
        CSR_WRITE_CHECK(addr, _pat, _pat, errs);    \
    }                                               \
} while (0)


#define TEST_BACK_TO_BACK(addr, errs) do {  \
    uint32_t _rd;                           \
    uint32_t _v1 = 0xAAAAAAAA;              \
    uint32_t _v2 = 0x55555555;              \
    CSR_WRITE(addr, _v1);                   \
    CSR_WRITE(addr, _v2);                   \
    CSR_READ(addr, _rd);                    \
    if (_rd != _v2) {                       \
        (errs)++;                           \
    }                                       \
} while (0)


#define TEST_IDEMPOTENT(addr, errs) do {                              \
    uint32_t _val = 0x600DC512;                                       \
    CSR_WRITE_CHECK(addr, _val, _val, errs);                          \
    CSR_WRITE_CHECK(addr, _val, _val, errs);                          \
} while (0)


#define TEST_PSEUDO_RANDOM(addr, errs) do {                           \
    CSR_WRITE_CHECK(addr, 0x600DC512, 0x600DC512, errs);              \
    CSR_WRITE_CHECK(addr, 0x0BADC512, 0x0BADC512, errs);              \
    CSR_WRITE_CHECK(addr, 0x12345678, 0x12345678, errs);              \
    CSR_WRITE_CHECK(addr, 0x87654321, 0x87654321, errs);              \
} while (0)


#define TEST_RESTORE(addr, saved, errs) do {                          \
    CSR_WRITE_CHECK(addr, saved, saved, errs);                        \
} while (0)


#define RUN_ALL_CSR_TESTS(addr, reset_val, errs) do {                 \
    uint32_t _saved;                                                  \
    CSR_READ(addr, _saved);                                           \
                                                                      \
    TEST_RESET_VALUE(addr, reset_val, errs);                          \
                                                                      \
    TEST_BASIC_PATTERNS(addr, errs);                                  \
                                                                      \
    TEST_WALKING_ONES(addr, errs);                                    \
                                                                      \
    TEST_WALKING_ZEROS(addr, errs);                                   \
                                                                      \
    TEST_BACK_TO_BACK(addr, errs);                                    \
                                                                      \
    TEST_IDEMPOTENT(addr, errs);                                      \
                                                                      \
    TEST_PSEUDO_RANDOM(addr, errs);                                   \
                                                                      \
    TEST_RESTORE(addr, _saved, errs);                                 \
} while (0)


int main(void)
{
    int errors = 0;

    /*
     * MSCRATCH (0x340) - Machine Scratch Register
     * RTL: cs_registers_i.mscratch_q
     */
    RUN_ALL_CSR_TESTS(0x340, 0x00000000, errors);

    *RESULT_REG = (errors == 0) ? PASS_VALUE : FAIL_VALUE;

    asm volatile("wfi");
    while (1) {}  /* safety: halt if wfi returns on spurious wakeup */
}
