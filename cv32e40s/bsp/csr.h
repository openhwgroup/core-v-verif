/*
**
** Copyright 2021 OpenHW Group
** Copyright 2021 Silicon Labs
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
**
** CV32E40S CSR header file
**
** Generated with gen_csr_header.py
**
*******************************************************************************
*/

#ifndef CV32E40S_H_
#define CV32E40S_H_

#define MCYCLE           0xB00
#define MCYCLEH          0xB80
#define MINSTRET         0xB02
#define MINSTRETH        0xB82
#define CYCLE            0xC00
#define CYCLEH           0xC80
#define INSTRET          0xC02
#define INSTRETH         0xC82
#define TIME             0xC01
#define TIMEH            0xC81
#define MHPMCOUNTER3     0xB03
#define MHPMCOUNTER3H    0xB83
#define MHPMCOUNTER4     0xB04
#define MHPMCOUNTER4H    0xB84
#define MHPMCOUNTER5     0xB05
#define MHPMCOUNTER5H    0xB85
#define MHPMCOUNTER6     0xB06
#define MHPMCOUNTER6H    0xB86
#define MHPMCOUNTER7     0xB07
#define MHPMCOUNTER7H    0xB87
#define MHPMCOUNTER8     0xB08
#define MHPMCOUNTER8H    0xB88
#define MHPMCOUNTER9     0xB09
#define MHPMCOUNTER9H    0xB89
#define MHPMCOUNTER10    0xB0A
#define MHPMCOUNTER10H   0xB8A
#define MHPMCOUNTER11    0xB0B
#define MHPMCOUNTER11H   0xB8B
#define MHPMCOUNTER12    0xB0C
#define MHPMCOUNTER12H   0xB8C
#define MHPMCOUNTER13    0xB0D
#define MHPMCOUNTER13H   0xB8D
#define MHPMCOUNTER14    0xB0E
#define MHPMCOUNTER14H   0xB8E
#define MHPMCOUNTER15    0xB0F
#define MHPMCOUNTER15H   0xB8F
#define MHPMCOUNTER16    0xB10
#define MHPMCOUNTER16H   0xB90
#define MHPMCOUNTER17    0xB11
#define MHPMCOUNTER17H   0xB91
#define MHPMCOUNTER18    0xB12
#define MHPMCOUNTER18H   0xB92
#define MHPMCOUNTER19    0xB13
#define MHPMCOUNTER19H   0xB93
#define MHPMCOUNTER20    0xB14
#define MHPMCOUNTER20H   0xB94
#define MHPMCOUNTER21    0xB15
#define MHPMCOUNTER21H   0xB95
#define MHPMCOUNTER22    0xB16
#define MHPMCOUNTER22H   0xB96
#define MHPMCOUNTER23    0xB17
#define MHPMCOUNTER23H   0xB97
#define MHPMCOUNTER24    0xB18
#define MHPMCOUNTER24H   0xB98
#define MHPMCOUNTER25    0xB19
#define MHPMCOUNTER25H   0xB99
#define MHPMCOUNTER26    0xB1A
#define MHPMCOUNTER26H   0xB9A
#define MHPMCOUNTER27    0xB1B
#define MHPMCOUNTER27H   0xB9B
#define MHPMCOUNTER28    0xB1C
#define MHPMCOUNTER28H   0xB9C
#define MHPMCOUNTER29    0xB1D
#define MHPMCOUNTER29H   0xB9D
#define MHPMCOUNTER30    0xB1E
#define MHPMCOUNTER30H   0xB9E
#define MHPMCOUNTER31    0xB1F
#define MHPMCOUNTER31H   0xB9F
#define HPMCOUNTER3      0xC03
#define HPMCOUNTER3H     0xC83
#define HPMCOUNTER4      0xC04
#define HPMCOUNTER4H     0xC84
#define HPMCOUNTER5      0xC05
#define HPMCOUNTER5H     0xC85
#define HPMCOUNTER6      0xC06
#define HPMCOUNTER6H     0xC86
#define HPMCOUNTER7      0xC07
#define HPMCOUNTER7H     0xC87
#define HPMCOUNTER8      0xC08
#define HPMCOUNTER8H     0xC88
#define HPMCOUNTER9      0xC09
#define HPMCOUNTER9H     0xC89
#define HPMCOUNTER10     0xC0A
#define HPMCOUNTER10H    0xC8A
#define HPMCOUNTER11     0xC0B
#define HPMCOUNTER11H    0xC8B
#define HPMCOUNTER12     0xC0C
#define HPMCOUNTER12H    0xC8C
#define HPMCOUNTER13     0xC0D
#define HPMCOUNTER13H    0xC8D
#define HPMCOUNTER14     0xC0E
#define HPMCOUNTER14H    0xC8E
#define HPMCOUNTER15     0xC0F
#define HPMCOUNTER15H    0xC8F
#define HPMCOUNTER16     0xC10
#define HPMCOUNTER16H    0xC90
#define HPMCOUNTER17     0xC11
#define HPMCOUNTER17H    0xC91
#define HPMCOUNTER18     0xC12
#define HPMCOUNTER18H    0xC92
#define HPMCOUNTER19     0xC13
#define HPMCOUNTER19H    0xC93
#define HPMCOUNTER20     0xC14
#define HPMCOUNTER20H    0xC94
#define HPMCOUNTER21     0xC15
#define HPMCOUNTER21H    0xC95
#define HPMCOUNTER22     0xC16
#define HPMCOUNTER22H    0xC96
#define HPMCOUNTER23     0xC17
#define HPMCOUNTER23H    0xC97
#define HPMCOUNTER24     0xC18
#define HPMCOUNTER24H    0xC98
#define HPMCOUNTER25     0xC19
#define HPMCOUNTER25H    0xC99
#define HPMCOUNTER26     0xC1A
#define HPMCOUNTER26H    0xC9A
#define HPMCOUNTER27     0xC1B
#define HPMCOUNTER27H    0xC9B
#define HPMCOUNTER28     0xC1C
#define HPMCOUNTER28H    0xC9C
#define HPMCOUNTER29     0xC1D
#define HPMCOUNTER29H    0xC9D
#define HPMCOUNTER30     0xC1E
#define HPMCOUNTER30H    0xC9E
#define HPMCOUNTER31     0xC1F
#define HPMCOUNTER31H    0xC9F
#define DCSR             0x7B0
#define DPC              0x7B1
#define DSCRATCH0        0x7B2
#define DSCRATCH1        0x7B3
#define MSTATUS          0x300
#define MISA             0x301
#define MIE              0x304
#define MTVEC            0x305
#define MTVT             0x307
#define MSTATUSH         0x310
#define MCOUNTINHIBIT    0x320
#define MHPMEVENT3       0x323
#define MHPMEVENT4       0x324
#define MHPMEVENT5       0x325
#define MHPMEVENT6       0x326
#define MHPMEVENT7       0x327
#define MHPMEVENT8       0x328
#define MHPMEVENT9       0x329
#define MHPMEVENT10      0x32A
#define MHPMEVENT11      0x32B
#define MHPMEVENT12      0x32C
#define MHPMEVENT13      0x32D
#define MHPMEVENT14      0x32E
#define MHPMEVENT15      0x32F
#define MHPMEVENT16      0x330
#define MHPMEVENT17      0x331
#define MHPMEVENT18      0x332
#define MHPMEVENT19      0x333
#define MHPMEVENT20      0x334
#define MHPMEVENT21      0x335
#define MHPMEVENT22      0x336
#define MHPMEVENT23      0x337
#define MHPMEVENT24      0x338
#define MHPMEVENT25      0x339
#define MHPMEVENT26      0x33A
#define MHPMEVENT27      0x33B
#define MHPMEVENT28      0x33C
#define MHPMEVENT29      0x33D
#define MHPMEVENT30      0x33E
#define MHPMEVENT31      0x33F
#define MSCRATCH         0x340
#define MEPC             0x341
#define MCAUSE           0x342
#define MTVAL            0x343
#define MIP              0x344
#define MNXTI            0x345
#define MINTSTATUS       0xFB1
#define MINTTHRESH       0x347
#define MSCRATCHCSW      0x348
#define MSCRATCHCSWL     0x349
#define TSELECT          0x7A0
#define TDATA1           0x7A1
#define TDATA2           0x7A2
#define TDATA3           0x7A3
#define TINFO            0x7A4
#define TCONTROL         0x7A5
#define JVT              0x017
#define MVENDORID        0xF11
#define MARCHID          0xF12
#define MIMPID           0xF13
#define MHARTID          0xF14
#define MCONFIGPTR       0xF15
#define CPUCTRL          0xBF0
#define SECURESEED0      0xBF9
#define SECURESEED1      0xBFA
#define SECURESEED2      0xBFC
#define MCOUNTEREN       0x306
#define MENVCFG          0x30A
#define MSTATEEN0        0x30C
#define MSTATEEN1        0x30D
#define MSTATEEN2        0x30E
#define MSTATEEN3        0x30F
#define MENVCFGH         0x31A
#define MSTATEEN0H       0x31C
#define MSTATEEN1H       0x31D
#define MSTATEEN2H       0x31E
#define MSTATEEN3H       0x31F
#define MSECCFG          0x747
#define MSECCFGH         0x757
#define PMPCFG0          0x3A0
#define PMPCFG1          0x3A1
#define PMPCFG2          0x3A2
#define PMPCFG3          0x3A3
#define PMPCFG4          0x3A4
#define PMPCFG5          0x3A5
#define PMPCFG6          0x3A6
#define PMPCFG7          0x3A7
#define PMPCFG8          0x3A8
#define PMPCFG9          0x3A9
#define PMPCFG10         0x3AA
#define PMPCFG11         0x3AB
#define PMPCFG12         0x3AC
#define PMPCFG13         0x3AD
#define PMPCFG14         0x3AE
#define PMPCFG15         0x3AF
#define PMPADDR0         0x3B0
#define PMPADDR1         0x3B1
#define PMPADDR2         0x3B2
#define PMPADDR3         0x3B3
#define PMPADDR4         0x3B4
#define PMPADDR5         0x3B5
#define PMPADDR6         0x3B6
#define PMPADDR7         0x3B7
#define PMPADDR8         0x3B8
#define PMPADDR9         0x3B9
#define PMPADDR10        0x3BA
#define PMPADDR11        0x3BB
#define PMPADDR12        0x3BC
#define PMPADDR13        0x3BD
#define PMPADDR14        0x3BE
#define PMPADDR15        0x3BF
#define PMPADDR16        0x3C0
#define PMPADDR17        0x3C1
#define PMPADDR18        0x3C2
#define PMPADDR19        0x3C3
#define PMPADDR20        0x3C4
#define PMPADDR21        0x3C5
#define PMPADDR22        0x3C6
#define PMPADDR23        0x3C7
#define PMPADDR24        0x3C8
#define PMPADDR25        0x3C9
#define PMPADDR26        0x3CA
#define PMPADDR27        0x3CB
#define PMPADDR28        0x3CC
#define PMPADDR29        0x3CD
#define PMPADDR30        0x3CE
#define PMPADDR31        0x3CF
#define PMPADDR32        0x3D0
#define PMPADDR33        0x3D1
#define PMPADDR34        0x3D2
#define PMPADDR35        0x3D3
#define PMPADDR36        0x3D4
#define PMPADDR37        0x3D5
#define PMPADDR38        0x3D6
#define PMPADDR39        0x3D7
#define PMPADDR40        0x3D8
#define PMPADDR41        0x3D9
#define PMPADDR42        0x3DA
#define PMPADDR43        0x3DB
#define PMPADDR44        0x3DC
#define PMPADDR45        0x3DD
#define PMPADDR46        0x3DE
#define PMPADDR47        0x3DF
#define PMPADDR48        0x3E0
#define PMPADDR49        0x3E1
#define PMPADDR50        0x3E2
#define PMPADDR51        0x3E3
#define PMPADDR52        0x3E4
#define PMPADDR53        0x3E5
#define PMPADDR54        0x3E6
#define PMPADDR55        0x3E7
#define PMPADDR56        0x3E8
#define PMPADDR57        0x3E9
#define PMPADDR58        0x3EA
#define PMPADDR59        0x3EB
#define PMPADDR60        0x3EC
#define PMPADDR61        0x3ED
#define PMPADDR62        0x3EE
#define PMPADDR63        0x3EF


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mcycle_t;


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mcycleh_t;


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile minstret_t;


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile minstreth_t;


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile cycle_t;


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile cycleh_t;


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile instret_t;


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile instreth_t;


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile time_t;


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile timeh_t;


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mhpmcounter1h_t;


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mhpmcounter2h_t;


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mhpmcounter3h_t;


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile hpmcounter1h_t;


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile hpmcounter2h_t;


typedef union {
  struct {
      volatile uint32_t count : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile hpmcounter3h_t;


typedef union {
  struct {
      volatile uint32_t prv            : 2;
      volatile uint32_t step           : 1;
      volatile uint32_t nmip           : 1;
      volatile uint32_t mprven         : 1;
      volatile uint32_t v              : 1;
      volatile uint32_t cause          : 3;
      volatile uint32_t stoptime       : 1;
      volatile uint32_t stopcount      : 1;
      volatile uint32_t stepie         : 1;
      volatile uint32_t ebreaku        : 1;
      volatile uint32_t ebreaks        : 1;
      volatile uint32_t reserved_14_14 : 1;
      volatile uint32_t ebreakm        : 1;
      volatile uint32_t ebreakvu       : 1;
      volatile uint32_t ebreakvs       : 1;
      volatile uint32_t reserved_27_18 : 10;
      volatile uint32_t xdebugver      : 4;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile dcsr_t;


typedef union {
  struct {
      volatile uint32_t zero : 1;
      volatile uint32_t dpc  : 31;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile dpc_t;


typedef union {
  struct {
      volatile uint32_t scratch : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile dscratch_t;


typedef union {
  struct {
      volatile uint32_t reserved_0_0   : 1;
      volatile uint32_t sie            : 1;
      volatile uint32_t reserved_2_2   : 1;
      volatile uint32_t mie            : 1;
      volatile uint32_t reserved_4_4   : 1;
      volatile uint32_t spie           : 1;
      volatile uint32_t ube            : 1;
      volatile uint32_t mpie           : 1;
      volatile uint32_t spp            : 1;
      volatile uint32_t vs             : 2;
      volatile uint32_t mpp            : 2;
      volatile uint32_t fs             : 2;
      volatile uint32_t xs             : 2;
      volatile uint32_t mprv           : 1;
      volatile uint32_t sum            : 1;
      volatile uint32_t mxr            : 1;
      volatile uint32_t tvm            : 1;
      volatile uint32_t tw             : 1;
      volatile uint32_t tsr            : 1;
      volatile uint32_t reserved_30_23 : 8;
      volatile uint32_t sd             : 1;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mstatus_t;


typedef union {
  struct {
      volatile uint32_t a   : 1;
      volatile uint32_t b   : 1;
      volatile uint32_t c   : 1;
      volatile uint32_t d   : 1;
      volatile uint32_t e   : 1;
      volatile uint32_t f   : 1;
      volatile uint32_t g   : 1;
      volatile uint32_t h   : 1;
      volatile uint32_t i   : 1;
      volatile uint32_t j   : 1;
      volatile uint32_t k   : 1;
      volatile uint32_t l   : 1;
      volatile uint32_t m   : 1;
      volatile uint32_t n   : 1;
      volatile uint32_t o   : 1;
      volatile uint32_t p   : 1;
      volatile uint32_t q   : 1;
      volatile uint32_t r   : 1;
      volatile uint32_t s   : 1;
      volatile uint32_t t   : 1;
      volatile uint32_t u   : 1;
      volatile uint32_t v   : 1;
      volatile uint32_t w   : 1;
      volatile uint32_t x   : 1;
      volatile uint32_t y   : 1;
      volatile uint32_t z   : 1;
      volatile uint32_t mxl : 2;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile misa_t;


typedef union {
  union {
    struct {
      volatile uint32_t reserved_31_0  : 32;
    } __attribute__((packed)) volatile clic;
    struct {
      volatile uint32_t reserved_0_0   : 1;
      volatile uint32_t ssie           : 1;
      volatile uint32_t reserved_2_2   : 1;
      volatile uint32_t msie           : 1;
      volatile uint32_t reserved_4_4   : 1;
      volatile uint32_t stie           : 1;
      volatile uint32_t reserved_6_6   : 1;
      volatile uint32_t mtie           : 1;
      volatile uint32_t reserved_8_8   : 1;
      volatile uint32_t seie           : 1;
      volatile uint32_t reserved_10_10 : 1;
      volatile uint32_t meie           : 1;
      volatile uint32_t reserved_15_12 : 4;
      volatile uint32_t mfie           : 16;
    } __attribute__((packed)) volatile clint;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mie_t;


typedef union {
  union {
    struct {
      volatile uint32_t mode      : 2;
      volatile uint32_t submode   : 4;
      volatile uint32_t base_6    : 1;
      volatile uint32_t base_31_7 : 25;
    } __attribute__((packed)) volatile clic;
    struct {
      volatile uint32_t mode      : 2;
      volatile uint32_t base_6_2  : 5;
      volatile uint32_t base_31_7 : 25;
    } __attribute__((packed)) volatile clint;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mtvec_t;


typedef union {
  struct {
      volatile uint32_t reserved_5_0 : 6;
      volatile uint32_t base_n_1_6   : 1;
      volatile uint32_t base_31_n    : 25;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mtvt_t;


typedef union {
  struct {
      volatile uint32_t reserved_3_0  : 4;
      volatile uint32_t sbe           : 1;
      volatile uint32_t mbe           : 1;
      volatile uint32_t reserved_31_6 : 26;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mstatush_t;


typedef union {
  struct {
      volatile uint32_t cy             : 1;
      volatile uint32_t reserved_1_1   : 1;
      volatile uint32_t ir             : 1;
      volatile uint32_t selectors_31_4 : 29;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mcountinhibit_t;


typedef union {
  struct {
      volatile uint32_t scratch : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mscratch_t;


typedef union {
  struct {
      volatile uint32_t zero : 1;
      volatile uint32_t epc  : 31;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mepc_t;


typedef union {
  union {
    struct {
      volatile uint32_t exccode_10_0   : 11;
      volatile uint32_t exccode_30_11  : 20;
      volatile uint32_t interrupt      : 1;
    } __attribute__((packed)) volatile clint;
    struct {
      volatile uint32_t exccode_10_0   : 11;
      volatile uint32_t exccode_11     : 1;
      volatile uint32_t reserved_15_12 : 4;
      volatile uint32_t mpil           : 8;
      volatile uint32_t reserved_26_24 : 3;
      volatile uint32_t mpie           : 1;
      volatile uint32_t mpp            : 2;
      volatile uint32_t minhv          : 1;
      volatile uint32_t interrupt      : 1;
    } __attribute__((packed)) volatile clic;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mcause_t;


typedef union {
  struct {
      volatile uint32_t mtval : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mtval_t;


typedef union {
  struct {
      volatile uint32_t reserved_31_0  : 32;
      volatile uint32_t reserved_0_0   : 1;
      volatile uint32_t ssip           : 1;
      volatile uint32_t reserved_2_2   : 1;
      volatile uint32_t msip           : 1;
      volatile uint32_t reserved_4_4   : 1;
      volatile uint32_t stip           : 1;
      volatile uint32_t reserved_6_6   : 1;
      volatile uint32_t mtip           : 1;
      volatile uint32_t reserved_8_8   : 1;
      volatile uint32_t seip           : 1;
      volatile uint32_t reserved_10_10 : 1;
      volatile uint32_t meip           : 1;
      volatile uint32_t reserved_15_12 : 4;
      volatile uint32_t mfip           : 16;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mip_t;


typedef union {
  struct {
      volatile uint32_t mnxti : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mnxti_t;


typedef union {
  struct {
      volatile uint32_t uil            : 8;
      volatile uint32_t sil            : 8;
      volatile uint32_t reserved_23_16 : 8;
      volatile uint32_t mil            : 8;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mintstatus_t;


typedef union {
  struct {
      volatile uint32_t th            : 8;
      volatile uint32_t reserved_31_8 : 24;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mintthresh_t;


typedef union {
  struct {
      volatile uint32_t mscratchcsw : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mscratchcsw_t;


typedef union {
  struct {
      volatile uint32_t mscratchcswl : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mscratchcswl_t;


typedef union {
  struct {
      volatile uint32_t trigger : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile tselect_t;


typedef union {
  struct {
      volatile uint32_t info           : 16;
      volatile uint32_t reserved_31_16 : 16;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile tinfo_t;


typedef union {
  struct {
      volatile uint32_t reserved_2_0  : 3;
      volatile uint32_t mte           : 1;
      volatile uint32_t reserved_6_4  : 3;
      volatile uint32_t mpte          : 1;
      volatile uint32_t reserved_31_8 : 24;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile tcontrol_t;


typedef union {
  struct {
      volatile uint32_t mode       : 6;
      volatile uint32_t base_9_6   : 4;
      volatile uint32_t base_31_10 : 22;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile jvt_t;


typedef union {
  struct {
      volatile uint32_t id   : 7;
      volatile uint32_t bank : 25;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mvendorid_t;


typedef union {
  struct {
      volatile uint32_t id : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile marchid_t;


typedef union {
  struct {
      volatile uint32_t patch          : 4;
      volatile uint32_t reserved_7_4   : 4;
      volatile uint32_t minor          : 4;
      volatile uint32_t reserved_15_12 : 4;
      volatile uint32_t major          : 4;
      volatile uint32_t reserved_31_20 : 12;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mimpid_t;


typedef union {
  struct {
      volatile uint32_t hart : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mhartid_t;


typedef union {
  struct {
      volatile uint32_t reserved_31_0 : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mconfigptr_t;


typedef union {
  struct {
      volatile uint32_t dataindtiming  : 1;
      volatile uint32_t rnddummy       : 1;
      volatile uint32_t rndhint        : 1;
      volatile uint32_t pcharden       : 1;
      volatile uint32_t integrity      : 1;
      volatile uint32_t reserved_15_5  : 11;
      volatile uint32_t rnddummyfreq   : 4;
      volatile uint32_t reserved_31_20 : 12;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile cpuctrl_t;


typedef union {
  struct {
      volatile uint32_t seed : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile secureseed_t;


typedef union {
  struct {
      volatile uint32_t enable : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mcounteren_t;


typedef union {
  struct {
      volatile uint32_t fiom          : 1;
      volatile uint32_t reserved_3_1  : 3;
      volatile uint32_t cbie          : 2;
      volatile uint32_t cbcfe         : 1;
      volatile uint32_t cbze          : 1;
      volatile uint32_t reserved_31_8 : 24;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile menvcfg_t;


typedef union {
  struct {
      volatile uint32_t reserved_1_0  : 2;
      volatile uint32_t umjvt         : 1;
      volatile uint32_t reserved_31_3 : 29;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mstateen_t;


typedef union {
  struct {
      volatile uint32_t reserved_30_0 : 31;
      volatile uint32_t stce          : 1;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile menvcfgh_t;


typedef union {
  struct {
      volatile uint32_t zero : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mstateenh_t;


typedef union {
  struct {
      volatile uint32_t mml            : 1;
      volatile uint32_t mmwp           : 1;
      volatile uint32_t rlb            : 1;
      volatile uint32_t reserved_7_3   : 5;
      volatile uint32_t useed          : 1;
      volatile uint32_t sseed          : 1;
      volatile uint32_t reserved_31_10 : 22;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mseccfg_t;


typedef union {
  struct {
      volatile uint32_t zero : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile mseccfgh_t;


typedef union {
  struct {
      volatile uint32_t pmpcfg0_r      : 1;
      volatile uint32_t pmpcfg0_w      : 1;
      volatile uint32_t pmpcfg0_x      : 1;
      volatile uint32_t pmpcfg0_a      : 2;
      volatile uint32_t reserved_6_5   : 2;
      volatile uint32_t pmpcfg0_l      : 1;
      volatile uint32_t pmpcfg1_r      : 1;
      volatile uint32_t pmpcfg1_w      : 1;
      volatile uint32_t pmpcfg1_x      : 1;
      volatile uint32_t pmpcfg1_a      : 2;
      volatile uint32_t reserved_14_13 : 2;
      volatile uint32_t pmpcfg1_l      : 1;
      volatile uint32_t pmpcfg2_r      : 1;
      volatile uint32_t pmpcfg2_w      : 1;
      volatile uint32_t pmpcfg2_x      : 1;
      volatile uint32_t pmpcfg2_a      : 2;
      volatile uint32_t reserved_22_21 : 2;
      volatile uint32_t pmpcfg2_l      : 1;
      volatile uint32_t pmpcfg3_r      : 1;
      volatile uint32_t pmpcfg3_w      : 1;
      volatile uint32_t pmpcfg3_x      : 1;
      volatile uint32_t pmpcfg3_a      : 2;
      volatile uint32_t reserved_30_29 : 2;
      volatile uint32_t pmpcfg3_l      : 1;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile pmpcfg_t;


typedef union {
  struct {
      volatile uint32_t address_33_2 : 32;
  } __attribute__((packed)) volatile fields;
  volatile uint32_t raw;
} __attribute__((packed)) volatile pmpaddr_t;


#endif // CV32E40S_H_
