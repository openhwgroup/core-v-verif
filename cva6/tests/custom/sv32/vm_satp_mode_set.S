#=======================================================================
#      RW Access of satp to 
#      test whether SV-32 is working properly
#-----------------------------------------------------------------------
# Test Description:
# Verification of supported address translation scheme i.e sv32
# is selected by writing satp.mode=sv32 and reading back the satp/ This
# covers the following scenarios in both supervisor and user privilege
# modes for level1 PTE.
#                           level 1
#                   PTE setup with all permissions and satp access
#=======================================================================

#include "macros.h"

#ifdef smode
    #define SET_PTE_U 0
#else
    #define SET_PTE_U PTE_U
#endif

#define _MMODE_  "M"
#define _SUMODE_ "SU"

.text
.global _start
_start:
    ALL_MEM_PMP                                                             # PMP permission to all the memory    
    SATP_SETUP_SV32(pgtb_l1)                                                # set the SATP for virtualization

check_load:
    csrr t1, satp                                                           # tests the load access 
    srli t1, t1, 31															# t1 should be equal to 1
    nop
    j exit                                                                  # Jump to exit
                                                                   
trap_handler:

    csrr t0, mcause                                                         # read the value of mcause 
    la t1, rvtest_check                                                     # load the address of trvtest_check
    
    lw t2, 0(t1)                                                            # if cause expected then load 1 else 0
    lw t3, 4(t1)                                                            # load the expected value of mepc 
    lw t4, 8(t1)                                                            # load the expected value of mcause  

    li  t1, CAUSE_SUPERVISOR_ECALL                                          # load the value of supervisor ecall
    beq t0,t1,continue_in_m_mode                                            # checks if ecall is occured

    li  t1, CAUSE_USER_ECALL                                                # load the value of user ecall
    beq t0,t1,continue_in_m_mode                                            # checks for ecall is occured
    beqz t2, exit                                                           # Jumps to exit if cause is not expected
 
    csrr t5,mepc                                                            # read the value of mepc 
    bne t3,t5,exit                                                          # check the value of mepc with it's expected value

    bne  t0, t4, exit                                                       # jumps to exit if EXPECTED_CAUSE is'nt equal to mcause

    li t5, CAUSE_FETCH_PAGE_FAULT                                           # load the value of fetch page fault exception 
    beq t0,t5,continue_in_m_mode                                            # if fetch page fault jump to next instr in M mode

continue_execution:

    INCREMENT_MEPC   _SUMODE_                                               # update the value of mepc
    j trap_epilogs

continue_in_m_mode:

    INCREMENT_MEPC   _MMODE_                                                # update the value of mepc
    li t1,MSTATUS_MPP                                                       # update the MPP to MSTATUS_MPP for M mode
    csrs mstatus,t1                                                         # update the value mstatus MPP

trap_epilogs:

    la t1, rvtest_check                                                     # load the addr of rvtest_check
    li t2, 0
    sw t2, 0(t1)                                                            # Clear the expected cause
    sw t2, 4(t1)                                                            # Clear the exception PC
    sw t2, 8(t1)                                                            # Clear cause execution number
    mret

COREV_VERIF_EXIT_LOGIC                                                      # exit logic 

.data  
.align 24                                                                   # Superpage align  
    rvtest_check: 
      .word 0xdeadbeef                                                      # 1 for cause expected 0  for no cause 
      .word 0xbeefdead                                                      # write the value of mepc here (where  cause is expected)
      .word 0xcafecafe                                                      # write the value of expect cause 
.align 22                                     
    rvtest_data:   
      .word 0xbeefcafe                                                 
      .word 0xdeadcafe                                                 
      .word 0x00000000                                                 
      .word 0x00000000 
.align 12                                                      
    pgtb_l1:                                                       
        .zero 4096                                                 
    pgtb_l0:                                                       
        .zero 4096                                                                                                     

.align 4; .global tohost;   tohost:   .dword 0;
.align 4; .global fromhost; fromhost: .dword 0;