#include <fesvr/elf.h>
#include <fesvr/memif.h>

#include "Simulation.h"
#include "Types.h"
#include "riscv/mmu.h"

#include "svdpi.h"
#include <vpi_user.h>

#include <fcntl.h>
#include <memory>
#include <stdio.h>
#include <stdlib.h>
#include <string>
#include <sys/mman.h>
#include <sys/stat.h>
#include <vector>

#include <assert.h>
#include <iostream>
#include <map>
#include <unistd.h>

using namespace openhw;

Simulation *sim;
std::vector<std::pair<reg_t, mem_t *>> mem_cuts;

#define SHT_PROGBITS 0x1
#define SHT_GROUP 0x11

#define BOOTROM_BASE 0x10000
#define BOOTROM_SIZE 0x1000

std::vector<mem_cfg_t> memory_map;
Params params;

extern "C" void spike_set_default_params(const char *profile) {
  if (strcmp(profile, "cva6") == 0) {
    params.set("/top/", "isa", std::any(std::string("RV64GC")));
    params.set("/top/", "priv", any(std::string(DEFAULT_PRIV))); // MSU
    params.set("/top/", "num_procs", std::any(0x1UL));
    params.set("/top/", "bootrom", std::any(true));
    params.set("/top/", "generic_core_config", std::any(true));
    params.set("/top/", "dram_base", std::any(0x80000000UL));
    params.set("/top/", "dram_size", std::any(0x400UL * 1024 * 1024));
    params.set("/top/", "max_steps_enabled", std::any(false));
    params.set("/top/", "max_steps", std::any(2000000UL));

    params.set("/top/core/0/", "name", std::any(std::string("cva6")));
    params.set("/top/core/0/", "isa", std::any(std::string("RV64GC")));
  }
}

extern "C" void spike_set_param_uint64_t(const char *base, const char *name,
                                         uint64_t value) {
  params.set(base, name, value);
}
extern "C" void spike_set_param_str(const char *base, const char *name,
                                    const char *value) {
  params.set(base, name, std::string(value));
}
extern "C" void spike_set_param_bool(const char *base, const char *name,
                                     bool value) {
  params.set(base, name, std::any(value));
}

extern "C" void spike_create(const char *filename) {
  std::cerr << "[SPIKE] Starting 'spike_create'...\n";

  // TODO parse params from yaml
  string isa_str = std::any_cast<string>(params["/top/isa"]);

  cfg_t *config = new cfg_t(
      /*default_initrd_bounds=*/std::make_pair((reg_t)0, (reg_t)0),
      /*default_bootargs=*/nullptr,
      /*default_isa=*/isa_str.c_str(), // Built from the RTL configuration
      /*default_priv=*/DEFAULT_PRIV,   // TODO FIXME Ditto
      /*default_varch=*/DEFAULT_VARCH, // TODO FIXME Ditto
      /*default_misaligned=*/false,
      /*default_endianness*/ endianness_little,
      /*default_pmpregions=*/16,
      /*default_mem_layout=*/memory_map,
      /*default_hartids=*/std::vector<size_t>(),
      /*default_real_time_clint=*/false,
      /*default_trigger_count=*/4);

  // Define the default set of harts with their associated IDs.
  // If there are multiple IDs, the vector must be sorted in ascending
  // order and w/o duplicates, see 'parse_hartids' in spike_main/spike.cc.

  // FIXME FORNOW only a single hart with ID 0.
  std::vector<size_t> default_hartids;
  default_hartids.reserve(1); // Reserve nprocs() slots.
  default_hartids.push_back(0);
  config->hartids = default_hartids;

  if (!sim) {
    std::vector<std::string> htif_args;
    htif_args.push_back(std::string(filename));

    std::cerr << "[SPIKE] htif_args = {\n";
    for (auto s : htif_args)
      std::cerr << "  " << s << ",\n";
    std::cerr << "}\n";

    std::any a_num_procs = params["/top/num_procs"];
    ;
    uint64_t num_procs = a_num_procs.has_value()
                             ? std::any_cast<uint64_t>(a_num_procs)
                             : config->nprocs();
    std::any a_generic_config = params["/top/generic_core_config"];
    bool generic_config = a_generic_config.has_value()
                              ? std::any_cast<bool>(a_generic_config)
                              : false;

    mapParam coreParams = params.get_base("/top/cores/");

    std::vector<uint64_t> hartids = params.get_hartids();
    std::sort(hartids.begin(), hartids.end());

    uint64_t next_id =
        (hartids.size() == 0 ? 0 : hartids[hartids.size() - 1] + 1);

    for (size_t i = 0; i < (num_procs - hartids.size()); i++) {
      hartids.push_back(next_id + i);
    }

    config->hartids = hartids;

    if (generic_config) {
      for (size_t i = 0; i < num_procs; i++) {
        string base = "/top/core/" + std::to_string(hartids[i]) + "/";
        for (auto p : coreParams) {
          params.set(base, p.first, p.second);
        }
      }
    }

    sim = new Simulation((const cfg_t *)config, filename, params);

    // Disable the debug mode.
    sim->sim_t::set_debug(false);
  }
}

// Convert svOpenArrayHandle -> st_rvfi
void sv2rvfi(st_rvfi &rvfi, svOpenArrayHandle svOpen) {
  size_t size = svSize(svOpen, 1);
  uint64_t *array_ptr = (uint64_t *)svGetArrayPtr(svOpen);
  uint64_t *rvfi_ptr = (uint64_t *)&rvfi;

  for (size_t i = 0; i < size; i++) {
    rvfi_ptr[i] = array_ptr[size - i - 1];
  }
}

// Convert st_rvfi -> svOpenArrayHandle
void rvfi2sv(st_rvfi &rvfi, svOpenArrayHandle svOpen) {
  size_t size = sizeof(st_rvfi) / 8; // To match 64 byte fields
  uint64_t *array_ptr = (uint64_t *)svGetArrayPtr(svOpen);
  uint64_t *rvfi_ptr = (uint64_t *)&rvfi;

  for (size_t i = 0; i < size; i++) {
    array_ptr[size - i - 1] = rvfi_ptr[i];
  }
}

extern "C" void spike_step_struct(st_rvfi &reference, st_rvfi &spike) {
  std::vector<st_rvfi> vreference, vspike;
  vreference.push_back(reference);
  vspike = sim->step(1, vreference);
  spike = vspike[0];
}

extern "C" void spike_step_svOpenArray(svOpenArrayHandle reference,
                                       svOpenArrayHandle spike) {
  st_rvfi reference_rvfi, spike_rvfi;

  sv2rvfi(reference_rvfi, reference);
  spike_step_struct(reference_rvfi, spike_rvfi);
  rvfi2sv(spike_rvfi, spike);
}
