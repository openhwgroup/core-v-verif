#include "pmp.h"

// 32-bit arithmetic, use Schrage's method:
uint32_t lcg_parkmiller(uint32_t *state)
{
  // Precomputed parameters for Schrage's method
  const uint32_t M = 0x7fffffff;
  const uint32_t A = 48271;
  const uint32_t Q = M / A; // 44488
  const uint32_t R = M % A; //  3399

  uint32_t div = *state / Q; // max: M / Q = A = 48,271
  uint32_t rem = *state % Q; // max: Q - 1     = 44,487

  int32_t s = rem * A; // max: 44,487 * 48,271 = 2,147,431,977 = 0x7fff3629
  int32_t t = div * R; // max: 48,271 *  3,399 =   164,073,129
  int32_t result = s - t;

  if (result < 0)
    result += M;

  return *state = result;
}