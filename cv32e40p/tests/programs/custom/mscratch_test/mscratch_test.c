// Copyright (c) 2026 Anuj Pandey
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


/**
 * @file mscratch_test.c
 * @brief Functional test for RISC-V mscratch CSR (0x340) on CV32E40P.
 * Verifies CSRRW (write), CSRRS (set), and CSRRC (clear) operations 
 * using bitwise walking patterns and direct value comparisons.
 */

#include <stdio.h>
#include <stdlib.h>
/*

export CV_SIMULATOR=verilator
export CV_CORE=cv32e40p
export CV_SW_TOOLCHAIN=/opt/riscv
export CV_SW_PREFIX=riscv64-unknown-elf-
export CV_SW_MARCH=rv32imc_zicsr
export CV_SW_CFLAGS="-O2"
export CV_SW_CC=gcc

*/
void reset(){
	__asm__ volatile("csrrw x0, 0x340, x0");
}

void write_mscratch(int write){
	__asm__ volatile("csrrw x0, 0x340, %0" :: "r"(write));
}

void set_mscratch(int mask){
	__asm__ volatile("csrrs x0, 0x340, %0" :: "rm"(mask));
}

void clear_mscratch(int mask){
	__asm__ volatile("csrrc x0, 0x340, %0" :: "rm"(mask));
}
int read_mscratch(){
	unsigned int read=0;
	__asm__ volatile("csrrs %0, 0x340, x0" : "=r"(read));
	return read;
}

int main(int argc, char *argv[]){
  
  
 	unsigned int read;  // Read data
 	unsigned int write; // Write data
	unsigned int mask;   // Make value
	int test;
	unsigned int check;

	read=0;
	write=0;
	mask=0;
	test=0;
	check=0;
	
	printf("\n\nCustom Test\n");
	
	test++;
	write=0xBBBBBBBB;
	write_mscratch(write);
	read=read_mscratch();
	if(write!=read){
		printf("\nTest Failed at test=%d\n", test);
		return EXIT_FAILURE;
	}
	
	test++;
	write=0x88888888;
	write_mscratch(write);
	read=read_mscratch();
	if(write!=read){
		printf("\nTest Failed at test=%d\n", test);
		return EXIT_FAILURE;
	}
	
	
	test++;
	for(int i=0; i<32; i++){ //bitwise write
		write=1<<i;
		write_mscratch(write);
		read=read_mscratch();
		if(read!=write){
			printf("\nTest Failed at test=%d at loop=%d\n", test, i);
			return EXIT_FAILURE;
		}
	}
	
	
	reset();
	check=0;
	test++;
	for(int i=0; i<32; i++){ //bitwise set
		mask=1<<i;
		check|=1<<i;
		set_mscratch(mask);
		read=read_mscratch();
		if(read!=check){
			printf("\nTest Failed at test=%d at loop=%d\n", test, i);
			return EXIT_FAILURE;
		}
	}
	
	test++;
	for(int i=0; i<32; i++){ //bitwise clear
		mask=1<<i;
		check&=(~(1<<i));
		clear_mscratch(mask);
		read=read_mscratch();
		if(read!=check){
			printf("\nTest Failed at test=%d at loop=%d\n", test, i);
			return EXIT_FAILURE;
		}
	}
	
	
	printf("\nAll tests passed\n\n");
	
	
	return EXIT_SUCCESS;
}
