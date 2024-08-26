// See LICENSE for license details.
#ifndef _RISCV_CSRS_EXT_H
#define _RISCV_CSRS_EXT_H

#include "common.h"
#include "encoding.h"
// For reg_t:
#include "decode.h"
// For std::shared_ptr
#include <memory>
// For access_type:
#include "memtracer.h"
#include "csrs.h"
#include <unordered_map>
#include <map>
#include <cassert>
#include <string>

class processor_t;
namespace openhw {
class Processor;
}
struct state_t;

namespace openhw {
class reg {
public:
  reg(processor_t *const proc, const reg_t addr, reg_t init);

  virtual bool post_read(const reg_t &val) const noexcept;

  virtual bool pre_write(const reg_t &val) noexcept;

  virtual bool post_write(const reg_t &val) noexcept;

  bool custom_checks(insn_t insn, bool write) const;

  bool access_on_priv() const noexcept;

  void set_we(bool we) noexcept;

  bool get_we() noexcept;

  void set_param_write_mask(reg_t mask) noexcept;

  reg_t get_param_write_mask() noexcept;

  virtual bool unlogged_write(const reg_t val) noexcept;

  virtual reg_t unlogged_read() const noexcept;

  virtual void write(const reg_t val, const bool log = true) noexcept;

  virtual reg_t read() const noexcept;

  virtual void log_write() const noexcept;

  const reg_t address;

  virtual bool backdoor_write(const reg_t val) noexcept;

  virtual std::string get_name() noexcept;

  virtual void set_name(std::string new_name) noexcept;

  virtual void set_param_accessible(bool accessible) noexcept;

  virtual void set_param_implemented(bool implemented) noexcept;

private:
  reg_t value;

protected:
  reg_t param_write_mask;
  bool param_implemented;
  bool param_accessible;

  processor_t *const proc;
  state_t *const state;
  friend class Processor;

  static std::string addr2name(uint64_t addr);

  std::string name;
};


} // namespace openhw

#endif
