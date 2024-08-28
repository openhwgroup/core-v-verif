// See LICENSE for license details.

#include "Simulation.h"
#include "mmu.h"
#include <cassert>
#include <climits>
#include <cstdlib>
#include <inttypes.h>
#include <iostream>
#include <map>
#include <signal.h>
#include <sstream>
#include <stdio.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

using namespace openhw;

std::vector<std::pair<reg_t, abstract_device_t *>> plugin_devs;

void sim_thread_main(void *arg) {
  ((sim_t *)arg)->run();
  ((sim_t *)arg)->switch_to_host(); // To get the first point
}

// FIXME TODO Review settings of dm_config below.
debug_module_config_t dm_config = {.progbufsize = 2,
                                   .max_sba_data_width = 0,
                                   .require_authentication = false,
                                   .abstract_rti = 0,
                                   .support_hasel = true,
                                   .support_abstract_csr_access = true,
                                   .support_abstract_fpr_access = true,
                                   .support_haltgroups = true,
                                   .support_impebreak = true};

void Simulation::default_params(openhw::Params &params) {
  if (!params.exist("/top/", "generic_core_config"))
    params.set_bool("/top/", "generic_core_config", true, "true",
                    "Make generic configuration for all cores");
  if (!params.exist("/top/", "bootrom"))
    params.set_bool("/top/", "bootrom", true, "true",
                    "bootrom enable");
  if (!params.exist("/top/", "bootrom_base"))
    params.set_uint64_t("/top/", "bootrom_base", 0x10000UL,
                        "0x10000", "bootrom address");
  if (!params.exist("/top/", "bootrom_size"))
    params.set_uint64_t("/top/", "bootrom_size", 0x1000UL, "0x1000",
                        "bootrom size");

  if (!params.exist("/top/", "dram_enable"))
    params.set_bool("/top/", "dram_enable", true, "true", "DRAM enable");
  if (!params.exist("/top/", "dram_base"))
    params.set_uint64_t("/top/", "dram_base", 0x80000000UL,
                        "0x80000000", "DRAM base address");
  if (!params.exist("/top/", "dram_size"))
    params.set_uint64_t("/top/", "dram_size", 0x400UL * 1024 * 1024,
                        "0x40000000", "DRAM size");

  if (!params.exist("/top/", "log_commits"))
    params.set_bool("/top/", "log_commits", true, "True",
                    "Log commit enable");

  if (!params.exist("/top/", "max_steps_enabled"))
    params.set_bool("/top/", "max_steps_enabled", false, "False",
                    "Maximum steps enable");
  if (!params.exist("/top/", "max_steps_enabled"))
    params.set_bool("/top/", "max_steps_enabled", 200000UL, "200000",
                    "Maximum steps that the simulation can do ");

}

Simulation::Simulation(
    const cfg_t *cfg, bool halted, std::vector<std::pair<reg_t, mem_t *>> mems,
    std::vector<std::pair<reg_t, abstract_device_t *>> plugin_devices,
    const std::vector<std::string> &args,
    const debug_module_config_t &dm_config, const char *log_path,
    bool dtb_enabled, const char *dtb_file, bool socket_enabled,
    FILE *cmd_file, // needed for command line option --cmd
    openhw::Params &params)
    : sim_t(cfg, halted, mems, plugin_devices, args, dm_config, log_path,
            dtb_enabled, dtb_file, socket_enabled, cmd_file, params) {

  // It seems mandatory to set cache block size for MMU.
  // FIXME TODO: Use actual cache configuration (on/off, # of ways/sets).
  // FIXME TODO: Support multiple cores.
  get_core(0)->get_mmu()->set_cache_blocksz(reg_t(64));
  this->default_params(this->params);
  Params::parse_params("/top/", this->params, params);

  const std::vector<mem_cfg_t> layout;

  this->make_mems(layout);

  for (auto &x : this->mems)
    bus.add_device(x.first, x.second);

  string isa_str = (this->params["/top/isa"]).a_string;
  string priv_str = (this->params["/top/priv"]).a_string;
  this->isa = isa_parser_t(isa_str.c_str(), priv_str.c_str());
  this->reset();

  bool commitlog = (this->params["/top/log_commits"]).a_bool;
  this->configure_log(commitlog, commitlog);

  this->max_steps = (this->params["/top/max_steps"]).a_uint64_t;
  this->max_steps_enabled =
      (this->params["/top/max_steps_enabled"]).a_bool;

  target.init(sim_thread_main, this);
  host = context_t::current();
  target.switch_to(); // To get the first point
}

Simulation::Simulation(const cfg_t *cfg, string elf_path,
                       Params &params)
    : Simulation(cfg,                                      // cfg
                 false,                                    // halted
                 std::vector<std::pair<reg_t, mem_t *>>(), // mems
                 plugin_devs, std::vector<std::string>() = {elf_path},
                 dm_config,
                 "tandem.log", // log_path
                 false,         // dtb_enabled
                 nullptr,      // dtb_file
                 false,        // socket_enabled
                 NULL,         // cmd_file
                 params) {}

Simulation::~Simulation() {
}

int Simulation::run() {
  try {
    while (!sim_t::done()) {
      st_rvfi reference;
      std::vector<st_rvfi> vreference, vspike;
      vreference.push_back(reference);
      vspike = this->step(1, vreference);
    }
  } catch (std::ios_base::failure e) {
    std::cout << "[SPIKE] Max steps exceeded!" << std::endl;
  }
  return sim_t::exit_code();
}

void Simulation::make_mems(const std::vector<mem_cfg_t> &layout) {
  for (const auto &cfg : layout)
    mems.push_back(std::make_pair(cfg.get_base(), new mem_t(cfg.get_size())));

  bool bootrom = (this->params["/top/bootrom"]).a_bool;
  uint64_t bootrom_base =
      (this->params["/top/bootrom_base"]).a_uint64_t;
  uint64_t bootrom_size =
      (this->params["/top/bootrom_size"]).a_uint64_t;
  if (bootrom) {
    auto bootrom_device = std::make_pair(bootrom_base, new mem_t(bootrom_size));

    std::cerr << "[SPIKE] Initializing memories...\n";
    uint8_t rom_check_buffer[8] = {0, 0, 0, 0, 0, 0, 0, 0};
    // Populate the ROM.  Reset vector size is in 32-bit words and must be
    // scaled.
#include "bootrom.h"
    if (!bootrom_device.second->store(reg_t(0), reset_vec_size << 2,
                                      (const uint8_t *)reset_vec)) {
      std::cerr << "[SPIKE] *** ERROR: Failed to initialize ROM!\n";
      bootrom_device.second->load(reg_t(0), 8, rom_check_buffer);
      fprintf(stderr,
              "[SPIKE] ROM content head(8) = %02x %02x %02x %02x %02x %02x "
              "%02x %02x\n",
              rom_check_buffer[0], rom_check_buffer[1], rom_check_buffer[2],
              rom_check_buffer[3], rom_check_buffer[4], rom_check_buffer[5],
              rom_check_buffer[6], rom_check_buffer[7]);
    }

    this->mems.push_back(bootrom_device);
  }

  bool dram = (this->params["/top/dram_enable"]).a_bool;
  uint64_t dram_base = (this->params["/top/dram_base"]).a_uint64_t;
  uint64_t dram_size = (this->params["/top/dram_size"]).a_uint64_t;
  if (dram) {
    this->mems.push_back(std::make_pair(dram_base, new mem_t(dram_size)));
  }
}

std::vector<st_rvfi> Simulation::step(size_t n,
                                      std::vector<st_rvfi> &vreference) {

  // The state PC is the *next* insn fetch address.
  // Catch it before exec which yields a new value.
  std::vector<st_rvfi> vspike(n);
  for (size_t i = 0; i < n; i++) {
    if (i >= procs.size())
      continue;

    vspike[i] = ((Processor *)procs[i])->step(1, vreference[i]);
    vspike[i].halt = (sim_t::done() ? ((sim_t::exit_code() << 1) | 1) : 0);

    host = context_t::current();
    if (!sim_t::done()) {
      if (this->max_steps_enabled && (this->max_steps < this->total_steps)) {
        throw std::ios_base::failure("Max steps exceeded");
      }

      ++total_steps;
      target.switch_to();
    }
  }
  return vspike;
}

Processor* Simulation::get_core_by_id(size_t id) {
    for (size_t i = 0; i < procs.size(); i++) {
        if (procs[i]->get_id() == id)
            return (Processor*) procs[i];
    }
    return nullptr;
}

#if 0 // FORNOW Unused code, disable until needed.
void Simulation::set_debug(bool value)
{
  debug = value;
}

void Simulation::set_log(bool value)
{
  log = value;
}

void Simulation::set_histogram(bool value)
{
  histogram_enabled = value;
  for (size_t i = 0; i < procs.size(); i++) {
    procs[i]->set_histogram(histogram_enabled);
  }
}

void Simulation::set_procs_debug(bool value)
{
  for (size_t i=0; i< procs.size(); i++)
    procs[i]->set_debug(value);
}

bool Simulation::mmio_load(reg_t addr, size_t len, uint8_t* bytes)
{
  if (addr + len < addr)
    return false;
  return bus.load(addr, len, bytes);
}

bool Simulation::mmio_store(reg_t addr, size_t len, const uint8_t* bytes)
{
  if (addr + len < addr)
    return false;
  return bus.store(addr, len, bytes);
}

void Simulation::make_bootrom()
{
  start_pc = 0x80000000;

#include "bootrom.h"

  std::vector<char> rom((char*)reset_vec, (char*)reset_vec + sizeof(reset_vec));

  boot_rom.reset(new rom_device_t(rom));
  bus.add_device(DEFAULT_RSTVEC, boot_rom.get());
}

char* Simulation::addr_to_mem(reg_t addr) {
  auto desc = bus.find_device(addr);
  if (auto mem = dynamic_cast<mem_t*>(desc.second))
    if (addr - desc.first < mem->size())
      return mem->contents() + (addr - desc.first);
  return NULL;
}
#endif
