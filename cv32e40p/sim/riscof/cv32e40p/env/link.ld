OUTPUT_ARCH( "riscv" )
ENTRY(rvtest_entry_point)

SECTIONS
{
  . = 0x20000000;
  .tohost : { *(.tohost) }

  . = 0x80000000;
  .text.init : { *(.text.init) }
  . = ALIGN(0x1000);
  .text : { *(.text) }

  . = 0x80800000;
  .data : { *(.data) }
  .data.string : { *(.data.string)}
  .bss : { *(.bss) }
  _end = .;

  /* Below section is used as a mailbox location to send DUT testbench the symbol address
     of begin_signature and end_signature for each riscv_arch_test.
     Sail ref model default ram-size is 0x0400_0000 and to work within this, using a fixed
     offset of 0x03FF_1000 from the start of text.init section as mailbox addr.
     Note - if text.init section addr is changed above, then mailbox address to be changed
     accordingly to keep same offset wrt boot addr, to avoid modifying TB signature writer. */

  . = 0x83FF1000;
  .test_env_section : {
    __TEST_SIG_BEGIN_ADDR = .;
    LONG(0xDEADBEEF);
    __TEST_SIG_END_ADDR = .;
    LONG(0xDEADBEEF);
  }
}

