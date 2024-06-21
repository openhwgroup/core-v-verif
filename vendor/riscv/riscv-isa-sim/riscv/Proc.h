
#include "Types.h"
#include "processor.h"

namespace openhw {
typedef std::tuple<state_t, commit_log_mem_t> prev_changes_t;
class Processor : public processor_t {
public:
  Processor(const isa_parser_t *isa, const cfg_t *cfg, simif_t *sim,
            uint32_t id, bool halt_on_reset, FILE *log_file,
            std::ostream &sout_,
            Params &params); // because of command line option --log and -s we
                             // need both
  ~Processor();

  /*
   * Step function
   * *
   * * @param n:  Number of instructions to be finished
   * */
  st_rvfi step(size_t n, st_rvfi reference);


  /*
   * Revert the state of the processor to a previous state.
   * *
   * * @param num_steps:  Number of steps to revert
   * */
  void revert_step(uint32_t num_steps);

  /* 
   * Check if a given mip will trigger an interrupt.
   * * @param mip:  The value to be set
   * * @return:  True if interrupt will be taken, false if not
   * */
  bool will_trigger_interrupt(reg_t mip);

  /*
   * Externally inject an interrupt into Spike. This sets the mip register, and 
   * takes the interrupt if it is allowed to be taken, given the state and inputs. 
   * *
   * * @param mip:  The value to be set
   * * @param mie:  mie injected from external CSR
   * * @param revert_steps: Number of steps to revert if the interrupt will be taken. This is to account for pipeline flushes.
   * * @param interrupt_allowed: True if interrupt is allowed to be taken 
   * * @return:  True if interrupt will be taken, false if not
   * */
  bool interrupt(reg_t mip, reg_t mie, uint32_t revert_steps, bool interrupt_allowed);

  /*
   * Set the debug request
   * * 
   * * @param debug_req:  True if debug request is set
   * * @param revert_steps: Number of steps to revert if the debug request is taken
   * * @param debug_allowed: True if debug is allowed to be taken
   * */
  bool set_debug(bool debug_req, uint32_t revert_steps, bool debug_allowed);

  static void default_params(string base, openhw::Params &params);

  inline void set_XPR(reg_t num, reg_t value);
  inline void set_FPR(reg_t num, float128_t value);

protected:
  std::deque<prev_changes_t> previous_states;
  uint64_t max_previous_states;
  bool csr_counters_injection;
  bool taken_trap;
  uint32_t which_trap;
  reg_t next_rvfi_intr, next_debug;
  virtual void take_trap(trap_t &t, reg_t epc); // take an exception
};

} // namespace openhw
