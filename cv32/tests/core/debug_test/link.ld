/*
**
** Copyright 2020 OpenHW Group
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
*******************************************************************************
** This linker description file has two memory regions
**  1) debugger code is placed in dbg memory under the .debugger section
**  2) main memory is placed into ram memory
*******************************************************************************
*/


OUTPUT_FORMAT("elf32-littleriscv", "elf32-littleriscv",
	      "elf32-littleriscv")
OUTPUT_ARCH(riscv)
ENTRY(_start)
MEMORY
{
	/* All sections are placed into ram. */

	dbg (rwxai) : ORIGIN = 0x1A110800, LENGTH = 0x800
}

SECTIONS
{
        /* ----------------------------------------*/
        /* Debugger Code : This section address must be the same
           as the DM_HaltAddress parameter in the RTL*/
        .debugger (ORIGIN(dbg)):
        {
          KEEP(*(.debugger));
        } >dbg
        .debugger_exception (0x1A110C00):
        {
          KEEP(*(.debugger_exception));
        } >dbg
        /* Debugger Stack*/
        .debugger_stack         : ALIGN(16)
        {
         PROVIDE(__debugger_stack_start = .);
         . = 0x80;
        } >dbg
}

MEMORY
{
	/* All sections are placed into ram. */

	ram (rwxai) : ORIGIN = 0x00000000, LENGTH = 0x400000
}

SECTIONS
{

        /* ----------------------------------------*/
        /* we want a fixed entry point */
        PROVIDE(__boot_address = 0x80);

        /* stack and heap related settings */
        __stack_size = DEFINED(__stack_size) ? __stack_size : 0x400;
        PROVIDE(__stack_size = __stack_size);
        __heap_size = DEFINED(__heap_size) ? __heap_size : 0x400;


        /* Read-only sections, merged into text segment: */
        PROVIDE (__executable_start = SEGMENT_START("text-segment", 0x10000)); . = SEGMENT_START("text-segment", 0x10000) + SIZEOF_HEADERS;

        /* interrupt vectors */
        .vectors (ORIGIN(ram)):
        {
          PROVIDE(__vector_start = .);
          KEEP(*(.vectors));
        } >ram


        /* crt0 init code */
        .init (__boot_address):
        {
          KEEP (*(SORT_NONE(.init)))
          KEEP (*(.text.start))
        } >ram


	.text.init :
	{
		*(.text.init);
	} > ram

        /* the bulk of the program: main, libc, functions etc. */
	.text :
	{
		__ram_start = .;
		start*(.text);
		*(.text);
		__ram_end = .;
	} > ram
	_etext = .;

	.data :
	{
		__data_begin = .;
    		*(.data .data.* .gnu.linkonce.d.*)
	} > ram

	.data.string :
	{
		*(.data.string)
	} > ram

	.sdata :
	{
		__sdata_begin = .;
		*(.sdata .sdata.* .gnu.linkonce.s.*)
	} > ram
	_edata = .;

	. = ALIGN(4);
	__bss_start = .;
	.bss :
	{
		*(.bss)
	} > ram

	/* elf special section */
	.sbss :
	{
		*(.sbss)
	} > ram

	. = ALIGN(4);
	__bss_end = .;
	__global_pointer$ = MIN(__sdata_begin + 0x800,
			    MAX(__data_begin + 0x800, __bss_end - 0x800));
	_end = .;
        PROVIDE (end = .);

        /* heap: we should consider putting this to the bottom of the address space */
        .heap          :
        {
         PROVIDE(__heap_start = .);
         . = __heap_size;
         PROVIDE(__heap_end = .);
        } >ram


        /* stack: we should consider putting this further to the top of the address
          space */
        .stack         : ALIGN(16) /* this is a requirement of the ABI(?) */
        {
         PROVIDE(__stack_start = .);
         . = __stack_size;
         PROVIDE(_sp = .);
         PROVIDE(__stack_end = .);
        } >ram

        
}
