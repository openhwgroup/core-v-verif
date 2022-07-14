#include "pmp.h"

uint32_t calc_size(unsigned int cfg);
int calc_top(int cfg);
int calc_base(int cfg);

int calc_base(int cfg) {
  int base;
  if (calc_size(cfg) > cfg) {
    return 0;
  }
  base = ((cfg << 2) | 3) & ~(calc_size(cfg) - 1);
  return base;
}

int calc_top(int cfg) {
  int top;
  top = calc_base(cfg) | (calc_size(cfg) - 1);
  return top;
}

uint32_t calc_size(unsigned int in_cfg) {
  uint32_t size = 0;
  unsigned int lv = 0, c, cfg;
  cfg = in_cfg;

  for (c = 0; cfg; ++c)
  {
    lv = cfg;
    cfg &= cfg-1;

    if (lv == cfg)
      break;
    if (lv == 0U)
      break;
    if (cfg == 0U)
      break;
  }

  size = 1 << (c+2);
  return size;
}
