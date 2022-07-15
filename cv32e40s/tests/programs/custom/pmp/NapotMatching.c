// #include "pmp.h"

// #define ABOVEDEBUG 0x1a111801

// void lockpmpcfgx()
// {
//   uint32_t lock = (1 << 7) | (1 << 15) | (1 << 23) | (1 << 31);
//   // all pmpcfg.l to be locked
//   asm volatile("csrrw x0, 0x3a0, %0" ::"r"(lock));
//   asm volatile("csrrw x0, 0x3a1, %0" ::"r"(lock));
//   asm volatile("csrrw x0, 0x3a2, %0" ::"r"(lock));
//   asm volatile("csrrw x0, 0x3a3, %0" ::"r"(lock));
//   asm volatile("csrrw x0, 0x3a4, %0" ::"r"(lock));
//   asm volatile("csrrw x0, 0x3a5, %0" ::"r"(lock));
//   asm volatile("csrrw x0, 0x3a6, %0" ::"r"(lock));
//   asm volatile("csrrw x0, 0x3a7, %0" ::"r"(lock));
//   asm volatile("csrrw x0, 0x3a8, %0" ::"r"(lock));
//   asm volatile("csrrw x0, 0x3a9, %0" ::"r"(lock));
//   asm volatile("csrrw x0, 0x3aa, %0" ::"r"(lock));
//   asm volatile("csrrw x0, 0x3ab, %0" ::"r"(lock));
//   asm volatile("csrrw x0, 0x3ac, %0" ::"r"(lock));
//   asm volatile("csrrw x0, 0x3ad, %0" ::"r"(lock));
//   asm volatile("csrrw x0, 0x3ae, %0" ::"r"(lock));
//   asm volatile("csrrw x0, 0x3af, %0" ::"r"(lock));
// }

// extern uint32_t calc_size(uint32_t cfg);
// extern uint32_t calc_top(uint32_t cfg);
// extern uint32_t calc_base(uint32_t cfg);

// void store2addr(uint32_t input, uint32_t addr)
// {
  // sw var, 0(addr)
//   asm volatile("sw %0, 0(%1)" ::"r"(input), "r"(addr));
// }

// void load4addr(int output, uint32_t addr)
// {
//   asm volatile("lw %0, 0(%1)"
//                : "=r"(output)
//                : "r"(addr));
// }

// void napot_matching()
// {
//   uint32_t base_addr, top_addr, region_size, temp = 0;
//   int count = 0;
  // PMPXCFG pmpxcfg;
  // PMPCFGX pmpcfgx;
  // static CSRS csrs;
  // 2 set bits
  // unsigned int napot = ((1 << 4) | (1 << 3)), exe = 1 << 2, write = 1 << 1, read = 1;
  // set bit vlaues in pmpcfgx
  // uint32_t mode = (3 << 3) | (3 << 11) | (3 << 19) | (3 << 27);
  // uint32_t exe = (1 << 2) | (1 << 10) | (1 << 18) | (1 << 26);
  // uint32_t write = (1 << 1) | (1 << 9) | (1 << 17) | (1 << 25);
  // uint32_t read = (1 << 0) | (1 << 8) | (1 << 16) | (1 << 24);
  // uint32_t value;
  // make up space on the heap for operations
  // and space is where the NPAPOT starts

  // calculate the base of the space
  // base = calc_base(space);
  // top = calc_top(space);
  // region_size = calc_size(space);
  // base_addr = calc_base(0x20000000);
  // top_addr = calc_top(0x20000000);

  // printf("\t\n base addr 0x%x\n", base_addr);

  // store word to memory base_addr
  // for (uint32_t i = base_addr; i <= top_addr; i++)
  // {
    // store2addr(i - base_addr + 1, i);
  //   asm volatile("sw %0, 0(%1)" ::"r"(i - base_addr + 1), "r"(i));
  // }
  // printf("\t\n loop counts %d\n", count);

  // store2addr(10, 0x20000000);
  // store2addr(500, top_addr);

  // TODO: region for R
  // set pmp NAPOT addr to base
  // find the space, then configure
  // pmpcfg0 read
  // asm volatile("csrrw x0, 0x3b0, %0\n"
  //              "csrrw x0, 0x3a0,%1\n" ::"r"(0x20000000),
  //              "r"(napot | read));

  // reading from specified region
  // for (uint32_t i = base_addr; i < base_addr + 5; i++)
  // {
  //   int count=0;
  //   count++;
  // }
  // asm volatile("lw %0, 0(%1)"
  //              : "=r"(temp)
  //              : "r"(0x20000000));
  // printf("\t\n loading from address 0x%x\n", 0x20000000);
  // printf("\t\n value %d\n\n", temp);

  // asm volatile("lw %0, 0(%1)"
  //              : "=r"(temp)
  //              : "r"(0x20001044));
  // printf("\t\n loading from address 0x%x\n", 0x20001044);
  // printf("\t\n value %d\n\n", temp);

//   asm volatile("lw %0, 0(%1)"
//                : "=r"(temp)
//                : "r"(base_addr + 1));
//   printf("\t\n loading from address 0x%x\n", base_addr + 1);
//   printf("\t\n value %d\n\n", temp);

//   asm volatile("lw %0, 0(%1)"
//                : "=r"(temp)
//                : "r"(base_addr + 2));
//   printf("\t\n loading from address 0x%x\n", base_addr + 2);
//   printf("\t\n value %d\n\n", temp);

//   asm volatile("lw %0, 0(%1)"
//                : "=r"(temp)
//                : "r"(top_addr));
//   printf("\t\n store to address 0x%x\n", top_addr);
//   printf("\t\n loading value %d\n\n", temp);

//  asm volatile("lw %0, 0(%1)"
//                : "=r"(temp)
//                : "r"(top_addr + 2));
//   printf("\t\n loading from address 0x%x\n", top_addr + 2);
//   printf("\t\n value %d\n\n", temp);

  // printf("\n\tprinting reading value 0x%x\n\n", value);
  // TODO: region for RW
  // TODO: region for RX
  // TODO: region for X
  // TODO: region for RWX
// }
