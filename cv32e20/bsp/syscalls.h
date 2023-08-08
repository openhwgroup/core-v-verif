#ifndef SYSCALLS_H
#define SYSCALLS_H
#include "csr.h"
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

extern int errno;
extern volatile uint64_t tohost;
extern volatile uint64_t fromhost;

extern volatile uint64_t stdout_reg;

#define STDOUT_FILENO 1

/* It turns out that older newlib versions use different symbol names which goes
 * against newlib recommendations. Anyway this is fixed in later version.
 */
#if __NEWLIB__ <= 2 && __NEWLIB_MINOR__ <= 5
#define _sbrk sbrk
#define _write write
#define _close close
#define _lseek lseek
#define _read read
#define _fstat fstat
#define _isatty isatty
#endif

#ifndef SYS_execve
#define SYS_execve 59
#endif

void exit(int value);

#endif
