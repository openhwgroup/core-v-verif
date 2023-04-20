OUTPUT_ARCH( "riscv" )
ENTRY(rvtest_entry_point)

SECTIONS
{
  . = 0x20000000;
  .tohost : { *(.tohost) }
    
  . = 0x80000000;
  .text.init : { *(.text.init) }
/*  . = ALIGN(0x1000);
  .tohost : { *(.tohost) } */
  . = ALIGN(0x1000);
  .text : { *(.text) }

  . = 0x80800000;
/*  . = ALIGN(0x1000); */
  .data : { *(.data) }
  .data.string : { *(.data.string)}
  .bss : { *(.bss) }
  _end = .;
}

