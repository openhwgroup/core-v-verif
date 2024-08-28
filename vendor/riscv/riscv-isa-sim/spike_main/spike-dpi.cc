// See LICENSE for license details.

// xspike forks an xterm for spike's target machine console,
// preserving the current terminal for debugging.

#include "common.h"
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/wait.h>
#include <string.h>
#include <cstdio>
#include <climits>
#include <cstring>
#include <stdexcept>
#include <iostream>
#include "riscv_dpi.cc"

int main(int UNUSED argc, char** argv)
{

    for (int i = 0; i < argc; ++i) {
        std::cout << argv[i] << "\n";
    }
    if (argc > 1) {
      std::string binary;
      binary = argv[1];
      spike_set_param_bool("/top/core/0/", "csr_counters_injection", true);
      spike_set_param_str("/top/", "isa", "rv32imc");
      spike_set_param_str("/top/", "priv", "MSU");
      spike_set_param_str("/top/core/0/", "isa", "rv32imc");
      spike_set_param_str("/top/core/0/", "priv", "MSU");

      spike_create(binary.c_str());
      st_rvfi spike, reference;
      memset(&reference, 0, sizeof(st_rvfi));
      memset(&spike, 0, sizeof(st_rvfi));
      uint64_t max_steps = 100000;
      for(uint64_t i = 0; ((spike.halt & 1) == 0); i++ ) {
        spike_step_struct(reference, spike);
        uint64_t mstatus_value;
        spike_get_csr(0, 0x300, mstatus_value);
        i++;
      }
      spike_step_struct(reference, spike);
      spike_delete();
    }
}
