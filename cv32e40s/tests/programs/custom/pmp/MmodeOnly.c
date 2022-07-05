#include "pmp.h"

CSRS csrs;

void pmpcfgxtest()
{
  uint32_t randpmpcfgx;
  // csrs.pmpcfgx[0] = read_csr(0x3a0);
  // csrs.pmpcfgx[1] = read_csr(0x3a1);
  // csrs.pmpcfgx[2] = read_csr(0x3a2);
  // csrs.pmpcfgx[3] = read_csr(0x3a3);
  // csrs.pmpcfgx[4] = read_csr(0x3a4);
  // csrs.pmpcfgx[5] = read_csr(0x3a5);
  // csrs.pmpcfgx[6] = read_csr(0x3a6);
  // csrs.pmpcfgx[7] = read_csr(0x3a7);
  // csrs.pmpcfgx[8] = read_csr(0x3a8);
  // csrs.pmpcfgx[9] = read_csr(0x3a9);
  // csrs.pmpcfgx[10] = read_csr(0x3aa);
  // csrs.pmpcfgx[11] = read_csr(0x3ab);
  // csrs.pmpcfgx[12] = read_csr(0x3ac);
  // csrs.pmpcfgx[13] = read_csr(0x3ad);
  // csrs.pmpcfgx[14] = read_csr(0x3ae);
  // csrs.pmpcfgx[15] = read_csr(0x3af);
  // for (int i = 0; i < 15; i++)
  // {
  //   printf("\npmpcfgx[%d] = %x\n\n", i, csrs.pmpcfgx[i]);
  // }
  change_mode();
  printf("\npritning in U mode\n\n");
  printf("\nattempting writing or reading CSRS in U mode\n\n");
  // back from the trap, reading mstatus
  // int randpmpcfgx = read_csr(0x3a9);
  asm volatile("csrrs %0, mstatus, x0\n"
               : "=r"(randpmpcfgx));
  printf("\tout of  handler\n\n");
  // csrs.mstatus = read_csr(0x300); this is illegal!!!! LOOP
  __asm__ volatile("csrrs %0, mstatus, x0\n"
               : "=r"(csrs.mstatus));
  printf("\ncsrs.mstatus = x%lx\n", csrs.mstatus);

  if (csrs.mstatus == 0x1800)
  {
    printf("\nback in M mode\n\n");
    // int randpmpcfgx = read_csr(0x3a9);
    printf("\ncore is back to M mode\n\n");
    asm volatile("csrrs %0, 0x3A9, x0\n"
               : "=r"(randpmpcfgx));
    if (randpmpcfgx == csrs.pmpcfgx[9])
    {
      printf("\npmpcfg[9] value is not overwriten\n\n");
    }
    else
    {
      printf("\nXXXXX pmpcfg value is overwriten XXXXX\n\n");
      printf("\nXXXXX pmpcfg test failed XXXXX\n\n");
      exit(EXIT_FAILURE);
    }
  }
}

void mmode_only()
{
  // int *readdata; this is illegal!!!LOOOP

  // set pmp addr to 0xffff-ffff
  asm volatile(
      "li t0, 0xFFFFFFFF\n"
      "csrrw x0, pmpaddr0, t0\n"
      "li t0, ((1<<3)+7)\n"
      "csrrw x0, 0x3a0, t0\n");

  pmpcfgxtest();
  exit(EXIT_SUCCESS);
}
