#!/usr/bin/perl
# Copyright (C) 2024 EM Microelectronic US Inc.
# Copyright (C) 2024 Dolphin Design
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
# illegal_instr_generator_cv32e40p_v2.pl has usage :
#    - “./illegal_instr_generator_cv32e40p_v2.pl <int>”
#    - “./illegal_instr_generator_cv32e40p_v2.pl rv32f”
#    - “./illegal_instr_generator_cv32e40p_v2.pl rv32Xpulp”
# If first (legacy) option with int argument is selected, it produces a test approximately .
# 0.64*int instructions long, where all the instructions are illegal instructions that cannot
# compile or execute properly, and create a assembly file containing only illegal instructions
#
# The two other options 'rv32f' and 'rv32Xpulp' generates a test containing all possibly illegaly
# formed instructions with all the same fixed values for operands.
#
# The script works by randomly or determinely generating a set of instruction encodings and then uses the
# compiler to tell it if the instruction is decoded into something or assumed illegal.
#
# Required:
# - CV_SW_TOOLCHAIN defined (path of the toolchain used, that contains the bin folder)
# - CV_SW_PREFIX defined (e.g. riscv32-corev-elf-)
#

use Data::Dumper;

sub test_header {
    return "
.globl _start
.globl main
.globl exit
.globl debug
.section .text
.global u_sw_irq_handler


\#define TEST_PASS                      123456789
\#define TEST_FAIL                              1
\#define VIRT_PERIPH_STATUS_FLAG_ADDR  0x20000000

\#define EXPECTED_ILLEGAL_INSTRUCTIONS $expected_ill_number

main:
    li        t0, (0x1 << 3)
    csrs      mstatus, t0
    li        x31, 0x0

\#ifdef FPU
    li x5, 0x00003800
    csrw 0x300, x5 # MSTATUS FPU enable
\#endif

    \#\#\#\#\#\#\#\#\# GENERATED CODE BELOW \#\#\#\#\#\#\#\#\#
";
}

sub test_footer {
    return "
    \#\#\#\#\#\#\#\#\# END OF GENERATED CODE \#\#\#\#\#\#\#\#\#

    li x18, TEST_PASS
    li x16, EXPECTED_ILLEGAL_INSTRUCTIONS
    beq x31, x16, test_end
    li x18, TEST_FAIL

test_end:
    li x17, VIRT_PERIPH_STATUS_FLAG_ADDR
    sw x18,0(x17)
    j _exit

\# The \"sw_irq_handler\" is entered on each illegal instruction.  Clears
\# mepc and increments the illegal instruction count in x31.
u_sw_irq_handler:
    li x30, 0xf
    csrrc x29, mcause, x0
    and x30, x29, x30
    li x28, 2
    bne x30, x28, _exit
    csrrc x27, mepc, x0
    c.addi x27, 4
    csrrw x0, mepc, x27
    c.addi x31, 1
    mret

_exit:
    j _exit

debug:
    j _exit

    ";
}

# to simplify generation and make sure every illegal are reached for F extension, the generation is retricted to a small set of opcodes, and fixed values for rs1 and rd
sub F_gen {
    open OUT_FILE, '>', "illegal_instr_temp.S" or die "Can't open illegal_instr_temp.S";

    print OUT_FILE ".section .init\n";
    print OUT_FILE ".global _start\n";
    print OUT_FILE "_start:\n";

    my @rd_opcode_list = ( "287", "2a7", "2c3", "2c7", "2cb", "2cf", "2d3");
    my @rs1_func3_list = ( "50" .. "57" );
    my @func7_rs2_list = ( 0x000 .. 0xfff );

    my @func7_rs2_maddsub = ( "525", "545", "565" );
    my $rs1_func3_maddsub = "55";

    my $func7_rs2_load_store = "aaa";

    # FLW & FSW (h287 & h2A7) ony rm != 010 (rs1_rd not )should be generated, with fixed values for others.

    foreach my $opcode ( @rd_opcode_list ) {
        if ( $opcode =~ /^2c/) { # f[n]madd/sub
            foreach my $itr ( @func7_rs2_maddsub ) {
                print OUT_FILE (".word(0x" . $itr . $rs1_func3_maddsub . $opcode . ")\n");
            }
        } elsif ( $opcode eq "287" or $opcode eq "2a7" ) { # FLW / FSW
            foreach my $itr ( @rs1_func3_list ) {
                print OUT_FILE (".word(0x" . $func7_rs2_load_store . $itr . $opcode . ")\n");
            }
        } else { # every other F options
            foreach my $func7_rs2 ( @func7_rs2_list ) {
                foreach my $itr ( @rs1_func3_list ) {
                    print OUT_FILE (".word(0x" . sprintf("%03x", $func7_rs2) . $itr . $opcode . ")\n");
                }
            }
        }
    }

    close OUT_FILE;
}

sub Xpulp_gen {
    open OUT_FILE, '>', "illegal_instr_temp.S" or die "Can't open illegal_instr_temp.S";

    print OUT_FILE ".section .init\n";
    print OUT_FILE ".global _start\n";
    print OUT_FILE "_start:\n";

    my @func7_list = ( 0x00 .. 0xff );
    my @func4_list = ( 0x0 .. 0xf );

    # for Custom-0, only cv.elw can be illegal instruction if CLUSTER is not present
    print OUT_FILE (".word(0x5555350b)\n");

    # for Custom-1, three func3 values are illegal :
    print OUT_FILE (".word(0xaaa5552b)\n");
    print OUT_FILE (".word(0xaaa5652b)\n");
    print OUT_FILE (".word(0xaaa5752b)\n");

    # for func3 = 011 :
    my $custom1_rs2_rs1_func3 = "a53";
    my $custom1_opcode = "52b";

    # iteration are done below together with custom-3

    # for func3 = 100
    # bits [7:0] are either AB or 2B, func3 is fixed, and uimmL rs1 should not be zero
    my $custom1_rs1_func3 = "54";
    my $uimml = "555";
    foreach (@func4_list) {
        print OUT_FILE (".word(0x". $uimml . $custom1_rs1_func3 . sprintf("%01x", $_) . "2b" . ")\n");
        print OUT_FILE (".word(0x". $uimml . $custom1_rs1_func3 . sprintf("%01x", $_) . "ab" . ")\n");
    }

    # custom-2
    # for custom-2 three cases of illegal f2,func3 = {11,000} or {10,001}; f2,func3 = {11,001} & Is[4:2] != 0
    print OUT_FILE (".word(0xcaa5055b)\n");
    print OUT_FILE (".word(0x8aa5155b)\n");
    print OUT_FILE (".word(0xcaa5155b)\n");

    # custom-3
    my $custom3_opcode = "57b";
    my @custom3_rs2_rs1_func3_list = ( "a50" .. "a57" );

    # iteration for custom1 func3 011 & custom3
    foreach my $f7 (@func7_list) {
        print OUT_FILE (".word(0x". sprintf("%02x", $f7) . $custom1_rs2_rs1_func3 . $custom1_opcode . ")\n");
        foreach my $c3 (@custom3_rs2_rs1_func3_list) {
            print OUT_FILE (".word(0x". sprintf("%02x", $f7) . $c3 . $custom3_opcode . ")\n");
        }
    }

    close OUT_FILE;
}

sub all_gen_rand {
    my $nb_instr = $_[0];

    open OUT_FILE, '>', "illegal_instr_temp.S" or die "Can't open illegal_instr_temp.S";

    print OUT_FILE ".section .init\n";
    print OUT_FILE ".global _start\n";
    print OUT_FILE "_start:\n";

    my @set = ('0' .. '9', 'a' .. 'f');
    for ($i = 0; $i<$nb_instr; $i++){
    $str = join '' => map $set[rand @set], 1 .. 8;
    $str = (".word(0x" . $str . ")");
    print OUT_FILE ("$str\n");
    }
    close OUT_FILE;
}

my $march = "rv32imc_zicsr";

# gen using rand method as before
if ($ARGV[0] eq "rv32f" ) {
    F_gen();
    $march = "rv32imfc";
} elsif ($ARGV[0] eq "rv32Xpulp" ) {
    Xpulp_gen();
    $march = "rv32imc_zicsr_zifencei_xcvhwlp1p0_xcvmem1p0_xcvmac1p0_xcvbi1p0_xcvalu1p0_xcvsimd1p0_xcvbitmanip1p0";
} else {
    all_gen_rand($ARGV[0]);
}

$cmd = ("-Os -g -D__riscv__=1 -D__LITTLE_ENDIAN__=1 -march=$march -Wa,-march=$march -fdata-sections -ffunction-sections -fdiagnostics-color=always");
#print ("Compiling list of interrupted instructions (interrupted_instructions.S) into an object file (interrupted_instructions.o)\n");
print "$ENV{CV_SW_TOOLCHAIN}/bin/$ENV{CV_SW_PREFIX}gcc ${cmd} -o illegal_instr_temp.o -c illegal_instr_temp.S\n";
`$ENV{CV_SW_TOOLCHAIN}/bin/$ENV{CV_SW_PREFIX}gcc ${cmd} -o illegal_instr_temp.o -c illegal_instr_temp.S`;
#print ("Compiling list of objects (interrupted_instructions.o) into an objdump file (interrupted_instructions.objdump)\n");
`$ENV{CV_SW_TOOLCHAIN}/bin/$ENV{CV_SW_PREFIX}objdump -D --disassemble=_start illegal_instr_temp.o > illegal_instr_temp.objdump`;

open my $fh, '<', "illegal_instr_temp.objdump" or die "Can't open illegal_instr_temp.S";

if ($ARGV[0] ne "rv32f" and $ARGV[0] ne "rv32Xpulp") {
    while(<$fh>){
        chomp;
        s/^\s+//;
        @fields = split(/\s+/);
        if ( $fields[0] =~ /^[a-f0-9]+\:/ and ($fields[2] eq ".insn" or $fields[3] =~ /unknown/) ) {
            $str = ".word(0x" . $fields[1] . ")";
            $illegal_instr{$str} = 1;
        }
    }
} else {
    while(<$fh>){
        chomp;
        s/^\s+//;
        @fields = split(/\s+/);
        if ( $fields[0] =~ /^[a-f0-9]+\:/ and ($fields[2] eq ".insn" or $fields[3] =~ /unknown/) ) {
            $str = ".word(0x" . $fields[1] . ")";
            $illegal_instr{$str} = 1;
        }
    }
}

our $expected_ill_number = scalar keys %illegal_instr;

close $fh;
open my $fh, '<', "illegal_instr_temp.S" or die "Can't open illegal_instr_temp.S for parsing";
open OUT_FILE, '>', "illegal_instr_test.S" or die "Can't open illegal_instr_test.S";

print ($expected_ill_number . " illegal instructions generated\n");

print OUT_FILE test_header();

while(<$fh>){
   chomp;
   $comp_string = $_;
   if(exists($illegal_instr{$comp_string})){
      print OUT_FILE " "x4 . "$comp_string\n";
   }
}
close $fh;

print OUT_FILE test_footer();

close OUT_FILE;

`$ENV{CV_SW_TOOLCHAIN}/bin/$ENV{CV_SW_PREFIX}gcc ${cmd} -o illegal_instr_test.o -c illegal_instr_test.S`;
`$ENV{CV_SW_TOOLCHAIN}/bin/$ENV{CV_SW_PREFIX}objdump -xd illegal_instr_test.o > illegal_instr_test.objdump`;
`rm -f illegal_instr_temp.o illegal_instr_temp.objdump illegal_instr_temp.S illegal_instr_test.o`;
