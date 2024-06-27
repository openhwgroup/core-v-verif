///////////////////////////////////////////////////////////////////////////////////////////
//                                                                                       //
//    Filename:  test1.S                     Test Name: Divide by Zero                   //
//                                                                                       //
//    Description:                                                                       //
//                Any floating point number divided by zero should set the DZ flag       //
//                of the FCSR                                                            //
//                                                                                       //
///////////////////////////////////////////////////////////////////////////////////////////
#include "riscv_test.h"

RVTEST_RV32UF
RVTEST_CODE_BEGIN

	j test_start

crash_backward:
	RVTEST_FAIL

test_start:
    ecall;
    li t0, 0x2000

    csrrs zero, mstatus, t0   # FS field of the mstatus must be set to 'initial'
    
    li t0, 0x4048F5C3     # Load the bit pattern for 3.14 into t0
    fmv.w.x f1, t0        # Move the value from t0 to f0 as a floating-point number

    li t0, 0              # Load the bit pattern for 0 into t0
    fmv.w.x f2, t0        # Move the value from t0 to f0 as a floating-point number

    fdiv.s f2, f1, f2     # Dividing a floating point number by zero, the flag in fcsr should update 

    frcsr a0              # Reading the fcsr

    j test_end

mtvec_handler:
    csrr t0, mepc
    addi t0, t0, 4
    csrw mepc, t0
    mret

crash_forward:
	RVTEST_FAIL

test_end:
	RVTEST_PASS

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN
 
.balign 16
ld_addr:
.dword 0xdeadbeefcafebabe
.dword 0xdeadbeefcafebabe

RVTEST_DATA_END
