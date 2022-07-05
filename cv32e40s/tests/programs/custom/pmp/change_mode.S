.section .text

.global change_mode
// .global user_code
// .global rwcsrs


change_mode:
  // to U mode if =0
  // beq a0, x0, umode
  // to M mode if !=0
  // bne a0, x0, mmode

umode:
  addi sp, sp, -4
  sw s0, 0(sp)
  // set mstatus to U mode
  // 1: auipc t0, %pcrel_hi(
  li t0, 0x1800
  csrrc x0, 0x300, t0
  // assing ra to mepc
  csrrw x0, 0x341, ra
  la a0, umode_msg
  jal ra, puts

  lw s0, 4(sp)
  add sp, sp, 4
  // return to next line in main
  mret

// mmode:
//   // set mstatus to U mode
//   li x5, 0x1800
//   csrrs x0, 0x300, x5
//   // assing ra to mepc
//   csrrw x0, 0x341, x1
//   la x10, mmode_msg
//   jal x1, puts
//   // return to next line in main
//   mret

.section .rodata
umode_msg:
  .string "\nuuuuu Switing to U mode uuuuu"

// mmode_msg:
//   .string "\nMMMMM Switing to M mode MMMMM"
