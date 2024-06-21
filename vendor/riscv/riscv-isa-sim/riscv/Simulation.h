// See LICENSE for license details.

#ifndef _SIM_SPIKE_H
#define _SIM_SPIKE_H

#include "Types.h"
#include "cfg.h"
#include "debug_module.h"
#include "devices.h"
#include "log_file.h"
#include "processor.h"
#include "sim.h"

#include <fesvr/context.h>
#include <fesvr/htif.h>
#include <map>
#include <memory>
#include <string>
#include <sys/types.h>
#include <thread>
#include <vector>

class mmu_t;
class remote_bitbang_t;
class socketif_t;

namespace openhw {
// this class encapsulates the processors in a RISC-V machine.
class Simulation : public sim_t {
protected:
public:
  bool standalone_mode;

  Simulation(const cfg_t *cfg, bool halted,
             std::vector<std::pair<reg_t, mem_t *>> mems,
             std::vector<std::pair<reg_t, abstract_device_t *>> plugin_devices,
             const std::vector<std::string> &args,
             const debug_module_config_t &dm_config, const char *log_path,
             bool dtb_enabled, const char *dtb_file, bool socket_enabled,
             FILE *cmd_file, // needed for command line option --cmd
             openhw::Params &params);
  Simulation(const cfg_t *cfg, string elf_path, Params &params);
  ~Simulation();

  void make_mems(const std::vector<mem_cfg_t> &layout);

  static void default_params(openhw::Params &params);

  /*
   * Run function that runs the whole program while in standalone mode
   * */
  int run();

  /*
   * Step function
   * *
   * * @param n:  Number of instructions to be finished
   * *
   * */
  std::vector<st_rvfi> step(size_t n, std::vector<st_rvfi> &vreference);

  /*
   * Set the MIP register
   * *
   * * @param mask:  The value to be set
   * * @param revert_steps: Number of steps to revert if the interrupt will be taken 
   * * @param interrupt_allowed: True if interrupt is allowed to be taken 
   * * @return:  True if interrupt will be taken, false if not
   * */
  bool interrupt(reg_t mask, reg_t mie, uint32_t revert_steps, bool interrupt_allowed);

  /*
   * Set the debug request
   * * 
   * * @param debug_req:  True if debug request is set
   * * @param revert_steps: Number of steps to revert if the debug request is taken
   * * @param debug_allowed: True if debug is allowed to be taken
   */
  bool set_debug_req(bool debug_req, uint32_t revert_steps, bool debug_allowed);

  /*
   * Revert the state  
   * *
   * * @param num_steps:  number of steps to revert
   * */
  void revert_state(int num_steps);

  /*
   * Proposed constuctor for the Simulation class
   * *
   * * @param params: parameters to configure the simulation behaviour
   * *
   * */
  Simulation(Params &params);

private:
  uint64_t total_steps = 0;
  uint64_t max_steps;
  bool max_steps_enabled;
};
} // namespace openhw

#endif
