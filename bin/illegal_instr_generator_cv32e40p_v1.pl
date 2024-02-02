#!/usr/bin/perl
# Copyright (C) 2024 EM Microelectronic US Inc.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# illegal_instr_generator_cv32e40p_v1.pl has usage “./illegal_instr_generator_cv32e40p_v1.pl <int>” 
# and produces a test approximately .09*int instructions long, where all the instructions are 
# illegal instructions that cannot compile or execute properly, and places the test in 
# ../application/exceptions.
#
# The script works by randomly generating a set of instruction encodings and then uses the 
# compiler to tell it if the instruction is decoded into something or assumed illegal.
# This is why only about 9% of the randomly generated encodings are actually illegal.
#
# To use the script replace <path to compiler> to the path of your compiler.
#

open OUT_FILE, '>', "illegal_instr_temp.S" or die "Can't open illegal_instr_temp.S";
my @set = ('0' .. '9', 'a' .. 'f');
for ($i = 0; $i<$ARGV[0]; $i++){
   $str = join '' => map $set[rand @set], 1 .. 8;
   $str = (".word(0x" . $str . ")");
   print OUT_FILE ("$str\n");
}
close OUT_FILE;

$cmd = ("-Os -g -D__riscv__=1 -D__LITTLE_ENDIAN__=1 -march=rv32imcxpulpv2 -Wa,-march=rv32imcxpulpv2 -fdata-sections -ffunction-sections -fdiagnostics-color=always");
#print ("Compiling list of interrupted instructions (interrupted_instructions.S) into an object file (interrupted_instructions.o)\n");
`<path to compiler>/riscv32-unknown-elf-gcc ${cmd} -o illegal_instr_temp.o -c illegal_instr_temp.S`;
#print ("Compiling list of objects (interrupted_instructions.o) into an objdump file (interrupted_instructions.objdump)\n");
`<path to compiler>/riscv32-unknown-elf-objdump -xd illegal_instr_temp.o > illegal_instr_temp.objdump`;

open my $fh, '<', "illegal_instr_temp.objdump" or die "Can't open illegal_instr_temp.S";
while(<$fh>){
   chomp;
   @fields = split(/\s+/);
   #print("$fields[3]\n");
   if($fields[3]=~/^0x[0-9a-f]{4,8}$/i){
      #print("$fields[3] is an illegal instruction\n");
      $str = (".word(0x" . $fields[2] . ")");
      $illegal_instr{$str} = 1;
   }
}
close $fh;

open my $fh, '<', "illegal_instr_temp.S" or die "Can't open illegal_instr_temp.S for parsing";
open OUT_FILE, '>', "illegal_instr_test.S" or die "Can't open illegal_instr_test.S";
print OUT_FILE (".globl _start\n.globl main\n.globl exit\n.globl debug\n.section .text\n.global test_results\ndebug:\n    j main\ntest_results:\n	.word 123456789\nmain:\n    li        t0, (0x1 << 3)\n    csrs      mstatus, t0\n");
while(<$fh>){
   chomp;
   $comp_string = $_;
   if(exists($illegal_instr{$comp_string})){
      print OUT_FILE "$comp_string\n";
   }
}
close $fh;
close OUT_FILE;
`<path to compiler>/riscv32-unknown-elf-gcc ${cmd} -o illegal_instr_test.o -c illegal_instr_test.S`;
`<path to compiler>/riscv32-unknown-elf-objdump -xd illegal_instr_test.o > illegal_instr_test.objdump`;
`cp illegal_instr_test.S ../application/exception/illegal_instr_test.S`;
`rm illegal_instr_temp.o illegal_instr_temp.objdump illegal_instr_temp.S illegal_instr_test.S illegal_instr_test.o`;
