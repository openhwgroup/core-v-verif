
#include "Types.h"
#include "processor.h"

namespace openhw {

  typedef struct {
      string name;
      bool override_mask_param;
      bool presence_param;
      bool write_enable_param;
      bool write_mask_param;
  } csr_param_t;


class Processor : public processor_t {
public:
  Processor(const isa_parser_t *isa, const cfg_t *cfg, simif_t *sim,
            uint32_t id, bool halt_on_reset, FILE *log_file,
            std::ostream &sout_,
            Params &params_); // because of command line option --log and -s we
                             // need both
  ~Processor();
  st_rvfi step(size_t n, st_rvfi reference);

  static void default_params(string base, openhw::Params &params, openhw::Processor *proc);

  inline uint64_t get_XPR(reg_t num);
  inline void set_XPR(reg_t num, reg_t value);
  inline void set_FPR(reg_t num, float128_t value);
  inline const Params& get_params() const { return params; }

  inline const string get_base() { return base; }

  void take_pending_interrupt();
  void take_interrupt(reg_t pending_interrupts);
  virtual void enter_debug_mode(uint8_t cause) override;

  void reset();

  bool any_custom_extensions() const override {
    if ((this->get_params()[base + "override_custom_extensions"]).a_bool)
        return (this->get_params()[base + "override_custom_extensions_value"]).a_bool;

    return !custom_extensions.empty();
  }

  virtual void put_csr(int which, reg_t val);

  virtual reg_t get_csr(int which, insn_t insn, bool write, bool peek = 0);

  virtual reg_t get_csr(int which);

  inline uint32_t mcause_to_mip(uint32_t mcause);

  inline uint64_t xlen_format(uint64_t value);

protected:
  bool nmi_inject;

  bool csr_counters_injection;

  bool taken_trap;
  bool taken_debug;
  uint64_t which_trap;
  uint64_t which_debug;

  string base;
  virtual void take_trap(trap_t &t, reg_t epc); // take an exception
  st_rvfi *reference;
  st_rvfi *step_rvfi;

  commit_log_reg_t last_log_reg_write;

  static std::unordered_map<char, std::tuple<uint64_t, uint64_t>> priv_ranges;

};

} // namespace openhw
