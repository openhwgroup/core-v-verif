.include "user_define.h"
.section .text.start
.globl _start
.section .text
#.include "user_init.s"
.type _start, @function

_start:
    j _start_main

.globl _start_main
.section .text
_start_main:

	#ifdef NO_PULP
	#define EXP_MISA 0x40001104
	#else
	#define EXP_MISA 0x40801104
	#endif

    # put all 1s into the register
    li x15, 0xffffffff       
    csrrw x11, 832, x15       # Write 0xFFFFFFFF to mscratch (832), read old to x11
    
    
    csrrs x11, 832, x0        
    li x15, 0xffffffff        
    bne x11, x15, csr_fail    # If mscratch != 0xFFFFFFFF, jump to fail

    # put all 0 
    
    li x15, 0x00000000        
    csrrw x11, 832, x15       
    
    # Read back to verify
    csrrs x11, 832, x0        
    li x15, 0x00000000        
    bne x11, x15, csr_fail    # If mscratch != 0x00000000, jump to fail
    
# took the pass and fail functions from a different test which also has the mscratch if it doesnt fail it will reach the pass and then just wfi

test_done:
    lui a0,print_port>>12
    addi a1,zero,'\n'
    sw a1,0(a0)
    addi a1,zero,'C'
    sw a1,0(a0)
    addi a1,zero,'V'
    sw a1,0(a0)
    addi a1,zero,'3'
    sw a1,0(a0)
    addi a1,zero,'2'
    sw a1,0(a0)
    addi a1,zero,' '
    sw a1,0(a0)
    addi a1,zero,'D'
    sw a1,0(a0)
    addi a1,zero,'O'
    sw a1,0(a0)
    addi a1,zero,'N'
    sw a1,0(a0)
    addi a1,zero,'E'
    sw a1,0(a0)
    addi a1,zero,'\n'
    sw a1,0(a0)
    sw a1,0(a0)



csr_pass:
    li x18, 123456789
    li x17, 0x20000000
    sw x18,0(x17)
    wfi

csr_fail:
    lui a0,print_port>>12    
    addi a1, zero, '\n'
    sw a1, 0(a0)
    addi a1, zero, 'C'
    sw a1, 0(a0)
    addi a1, zero, 'V'
    sw a1, 0(a0)
    addi a1, zero, '3'
    sw a1, 0(a0)
    addi a1, zero, '2'
    sw a1, 0(a0)
    addi a1, zero, ' '
    sw a1, 0(a0)
    addi a1, zero, 'F'
    sw a1, 0(a0)
    addi a1, zero, 'A'
    sw a1, 0(a0)
    addi a1, zero, 'I'
    sw a1, 0(a0)
    addi a1, zero, 'L'
    sw a1, 0(a0)
    addi a1, zero, ' '
    sw a1, 0(a0)
    
    # PRINT THE ERROR CODE (1-5)
    sw x29, 0(a0)             # Print the test ID stored in x29
    
    addi a1, zero, '\n'
    sw a1, 0(a0)
>>>>>>> ec9259f2 (Added more tests and prints a number based on which test failed)

    li x18, 1
    li x17, 0x20000000
    sw x18,0(x17)
    wfi
#
# end
#
