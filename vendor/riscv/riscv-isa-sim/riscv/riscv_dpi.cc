#include <fesvr/elf.h>
#include <fesvr/memif.h>

#include "riscv/mmu.h"
#include "Types.h"
#include "Simulation.h"

#include <vpi_user.h>
#include "svdpi.h"

#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <string>
#include <memory>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>

#include <assert.h>
#include <unistd.h>
#include <map>
#include <iostream>

using namespace openhw;

Simulation* sim;
std::vector<std::pair<reg_t, mem_t*>> mem_cuts;

#define SHT_PROGBITS 0x1
#define SHT_GROUP 0x11

#define BOOTROM_BASE 0x10000
#define BOOTROM_SIZE 0x1000

std::vector<mem_cfg_t> memory_map;
Params params;

extern "C" void spike_set_default_params(const char* profile)
{
    if (strcmp(profile, "cva6") == 0)
    {
        params.set("/top/", "isa", std::any(std::string("RV64GC")));
        params.set("/top/", "bootrom", std::any(true));
        params.set("/top/", "dram_base", std::any(0x80000000UL));
        params.set("/top/", "dram_size", std::any(0x64UL * 1024 * 1024));
        params.set("/top/", "max_steps_enabled", std::any(false));
        params.set("/top/", "max_steps", std::any(2000000UL));

        params.set("/top/core/0/", "name", std::any(std::string("cva6")));
        params.set("/top/core/0/", "isa", std::any(std::string("RV64GC")));
    }
}

extern "C" void spike_set_param_uint64_t(const char* base, const char* name, uint64_t value) { params.set(base, name, value); }
extern "C" void spike_set_param_str(const char* base, const char* name, const char* value) { params.set(base, name, std::string(value)); }

extern "C" void spike_create(const char* filename)
{
  std::cerr << "[Spike Tandem] Starting 'spike_create'...\n" ;

  // TODO parse params from yaml
  string isa_str = std::any_cast<string>(params["/top/isa"]);

  cfg_t *config = new
      cfg_t(/*default_initrd_bounds=*/std::make_pair((reg_t)0, (reg_t)0),
            /*default_bootargs=*/nullptr,
            /*default_isa=*/isa_str.c_str(),  // Built from the RTL configuration
            /*default_priv=*/DEFAULT_PRIV,   // TODO FIXME Ditto
            /*default_varch=*/DEFAULT_VARCH, // TODO FIXME Ditto
            /*default_misaligned=*/false,
            /*default_endianness*/endianness_little,
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

    sim = new Simulation((const cfg_t *)config, filename, params);

    // Disable the debug mode.
    sim->sim_t::set_debug(false);
  }
}

// advance Spike and get the retired instruction
extern "C" void spike_step(st_rvfi* rvfi)
{
  st_rvfi tmp_rvfi = sim->nstep(1);
  *rvfi = tmp_rvfi;
}

