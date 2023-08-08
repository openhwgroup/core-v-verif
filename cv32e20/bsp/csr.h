#ifndef CSR_H
#define CSR_H

#include "csr_encoding.h"
#include "syscalls.h"
#include <assert.h>
#include <errno.h>
#include <machine/syscall.h>
#include <newlib.h>
#include <sys/stat.h>
#include <sys/timeb.h>
#include <sys/times.h>
#include <sys/utime.h>
#include <unistd.h>

#undef errno
#ifndef __ASSEMBLER__

extern int errno;

typedef enum priv_enum { PRIV_M = 0x3, PRIV_S = 0x1, PRIV_U = 0x0 } priv_e;

inline const char *priv_to_string(priv_e val) {
  switch (val) {
  case PRIV_M:
    return "PRIV_M";
  case PRIV_S:
    return "PRIV_S";
  case PRIV_U:
    return "PRIV_U";
  default:
    return "PRIV";
  }
}

void set_status_pp(priv_e new_mode);

void return_to_machine();

void test_fail();

void test_pass();

#define BITS2SHIFT(mask) (mask & -mask)

#define csr_read(reg)                                                          \
  ({                                                                           \
    unsigned long __tmp;                                                       \
    asm volatile("csrr %0, " #reg : "=r"(__tmp));                              \
    __tmp;                                                                     \
  })

#define csr_write(reg, val) ({ asm volatile("csrw " #reg ", %0" ::"rK"(val)); })

#define csr_swap(reg, val)                                                     \
  ({                                                                           \
    unsigned long __tmp;                                                       \
    asm volatile("csrrw %0, " #reg ", %1" : "=r"(__tmp) : "rK"(val));          \
    __tmp;                                                                     \
  })

#define csr_set(reg, bit)                                                      \
  ({                                                                           \
    unsigned long __tmp;                                                       \
    asm volatile("csrrs %0, " #reg ", %1" : "=r"(__tmp) : "rK"(bit));          \
    __tmp;                                                                     \
  })

#define csr_clear(reg, bit)                                                    \
  ({                                                                           \
    unsigned long __tmp;                                                       \
    asm volatile("csrrc %0, " #reg ", %1" : "=r"(__tmp) : "rK"(bit));          \
    __tmp;                                                                     \
  })

#define csr_clear_mask(reg, mask) csr_clear(reg, BITS2SHIFT(mask))

#define csr_set_mask(reg, mask, value)                                         \
  ({                                                                           \
    unsigned long __tmp = csr_read(reg);                                       \
    __tmp = __tmp & mask;                                                      \
    __tmp |= (value << BITS2SHIFT(mask));                                      \
    csr_write(reg, __tmp);                                                     \
    __tmp;                                                                     \
  })

#define rdtime() csr_read(time)
#define rdcycle() csr_read(cycle)
#define rdinstret() csr_read(instret)

#endif

#endif
