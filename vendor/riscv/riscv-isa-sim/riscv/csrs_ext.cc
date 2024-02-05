// See LICENSE for license details.

// For std::any_of
#include <algorithm>

#include "csrs.h"
// For processor_t:
#include "mmu.h"
#include "processor.h"
// For get_field():
#include "decode_macros.h"
// For trap_virtual_instruction and trap_illegal_instruction:
#include "trap.h"
// For require():
#include "insn_macros.h"

// STATE macro used by require_privilege() macro:
#undef STATE
#define STATE (*state)

namespace openhw {
// implement a middle csr class
reg::reg(processor_t *const proc, const reg_t addr, const reg_t init)
    : address(addr), value(init), param_write_mask(-1), param_we(true),
      proc(proc), state(proc->get_state()) {}

void reg::set_we(bool we) noexcept { this->param_we = we; }

bool reg::get_we() noexcept { return this->param_we; }

void reg::set_param_write_mask(reg_t mask) noexcept {
  this->param_write_mask = mask;
}

reg_t reg::get_param_write_mask() noexcept { return this->param_write_mask; }

bool reg::post_read(const reg_t &val) const noexcept { return true; }

bool reg::pre_write(const reg_t &val) const noexcept {
  const reg_t curr = this->unlogged_read();
  const reg_t new_val =
      (val & this->param_write_mask) | (curr & ~this->param_write_mask);
  *((reg_t *)&val) = new_val;

  return true;
}
bool reg::post_write(const reg_t &val) const noexcept { return true; }

bool reg::custom_verify_permissions(insn_t insn, bool write) const {
  return true;
}

inline reg_t reg::unlogged_read() const noexcept {
  auto val = this->value;
  this->post_read(val);
  return val;
}

inline bool reg::unlogged_write(reg_t val) noexcept {
  this->value = val;
  return true;
}

void reg::write(const reg_t val) noexcept {
  if (!this->param_we)
    return;

  this->pre_write(val);
  const bool success = unlogged_write(val);
  this->post_write(val);

  if (success) {
    log_write();
  }
}
void reg::log_write() const noexcept {}

reg_t reg::read() const noexcept {
  auto val = this->unlogged_read();
  this->post_read(val);
  return val;
}

} // namespace openhw
