// Copyright (C) 2023 Thales DIS France SAS
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0.
//
// Original Author: Zbigniew CHAMSKI <zbigniew.chamski@thalesgroup.com>

#include "csrs.h"
#include "processor.h"
#include "cva6.h"
#include <cstdlib>

// Define CSR addresses.
#define CSR_ICACHE 0x7c0
#define CSR_DCACHE 0x7c1

// Define CSR field masks/values.
#define ICACHE_EN  0x1
#define DCACHE_EN  0x1

// This class instantiates the CV32A60X (CV32A6 "embedded") control&status extension.
class cv32a60x_extn_t : public cva6_extn_t
{
 public:
  const char* name() { return "cv32a60x"; }

  cv32a60x_extn_t()
  {
  }
  ~cv32a60x_extn_t() {}

  void reset()
  {
    std::cerr << "[Extension '" << name() << "'] reset()" << std::endl;

    // Complain if processor is not set.
    if (!p || !p->get_state()) {
      std::cerr << "ERROR: processor/state not set in cv32a60x_extn_t::reset()!" << std::endl;
      exit(1);
    }

    state_t *state = p->get_state();

    // Create ICACHE CSR.  Only bit 0 is writable. Initialize to 1.
    reg_t icache_mask = ICACHE_EN;
    state->csrmap[CSR_ICACHE] =
      icache_reg = std::make_shared<masked_csr_t>(p, CSR_ICACHE, icache_mask, 1);

    // Create DCACHE CSR.  Only bit 0 is writable. Initialize to 1.
    reg_t dcache_mask = DCACHE_EN;
    state->csrmap[CSR_DCACHE] =
      dcache_reg = std::make_shared<masked_csr_t>(p, CSR_DCACHE, dcache_mask, 1);
  }

private:
  // State variables go here.
  csr_t_p icache_reg = NULL;
  csr_t_p dcache_reg = NULL;

};

REGISTER_EXTENSION(cv32a60x, []() { return new cv32a60x_extn_t; })
