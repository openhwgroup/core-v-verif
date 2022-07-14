// #include <stdio.h>
// #include <stdlib.h>

#include "pmp.h"

// global variables in header as well
// CSRS glb_csrs;

// PMPXCFG glb_pmpxcfg;
// PMPCFGX glb_pmpcfgx;

// int setbits(int regvalue, char *fieldname)
// {
//   if (field == "pmpcfgxlock")
//   {
//     uint32_t lock = (1 << 7) | (1 << 15) | (1 << 23) | (1 << 31);
//     regvalue |= lock;
//     return regvalue;
//   }
// }

int main(int argc, char *argv[])
{
  // reset_registers();
  // default_full();
  // default_none();
  // mmode_only();
  napot_matching();

  exit(EXIT_SUCCESS);
}
