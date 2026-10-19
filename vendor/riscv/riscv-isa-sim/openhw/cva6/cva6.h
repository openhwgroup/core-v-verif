// Copyright (C) 2023 Thales DIS France SAS
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0.
//
// Original Author: Zbigniew CHAMSKI <zbigniew.chamski@thalesgroup.com>

#ifndef _CVA6_H
#define _CVA6_H

#include "extension.h"

class cva6_extn_t : public extension_t
{
 public:
  std::vector<insn_desc_t> get_instructions() override;
  std::vector<disasm_insn_t*> get_disasms() override;
  virtual void reset() override {};
};

#endif
