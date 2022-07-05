// #include <stdio.h>
// #include <stdlib.h>
#include "pmp.h"

void default_full()
{
  printf("\nxxxxx Checking DefaultFull xxxxxx\n");
  // initialize to 0
  uint32_t myarray[64] = {0};
  for (int i = 0; i < 64; i++)
  {
    if (myarray[i] != 0)
    {
      printf("\nInconsistant value to initializer!\n");
      printf("\nmyarray[%d] = %lx\n", i, myarray[i]);
      printf("\n");
      // exit(EXIT_FAILURE);
      exit(EXIT_FAILURE);
    }
  }

  for (int i = 0; i < 64; i++)
  {
    myarray[i] = i;
    // if (i == 10)
    // {
    //   myarray[i] = 11;
    // }

    if (myarray[i] != i)
    {
      printf("\nValues are not updated accordingly!\n");
      printf("Expected values = %d\n", i);
      printf("myarray[%d] = %lx\n", i, myarray[i]);
      printf("\n");
      exit(EXIT_FAILURE);
    }
  }
  printf("\nM-mode has the full access permissions.\n");
  printf("There's no exceptions to take care.\n");

  exit(EXIT_SUCCESS);
}