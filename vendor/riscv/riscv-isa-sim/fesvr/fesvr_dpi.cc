#include "config.h"
#include "elf.h"
#include "htif.h"
#include "htif_hexwriter.h"
#include "elfloader.h"
#include "memif.h"
#include "byteorder.h"
#include <cstring>
#include <string>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <assert.h>
#include <unistd.h>
#include <stdexcept>
#include <stdlib.h>
#include <stdio.h>
#include <vector>
#include <map>
#include <iostream>

#include <svdpi.h>

std::string loaded_binary;
// address and size
std::map<reg_t, reg_t> sections;
std::map<std::string, uint64_t> symbols;
// memory based address and content
std::map<reg_t, std::vector<uint8_t>> mems;
memif_t* memif;
htif_hexwriter_t *htif;
reg_t* entry;
int section_index = 0;

class dpi_memif_t : public memif_t {
public:
    dpi_memif_t (htif_t* htif) : memif_t(htif), htif(htif) {}

    void write(addr_t taddr, size_t len, const void* src) override
    {
        memif_t::write(taddr, len, src);

        sections[taddr] = len;
        uint64_t datum;
        uint8_t* buf = (uint8_t*) src;
        std::vector<uint8_t> mem;
        for (int i = 0; i < len; i++) {
            mem.push_back(buf[i]);
        }
        mems.insert(std::make_pair(taddr, mem));
    }
    void read(addr_t addr, size_t len, void* bytes) override
    {
        memif_t::read(addr, len, bytes);
    }

private:
    htif_t* htif;
};

// Communicate the section address and len
// Returns:
// 0 if there are no more sections
// 1 if there are more sections to load
extern "C" char get_section (long long* address, long long* len) {
    if (section_index < sections.size()) {
      auto it = sections.begin();
      for( int i = 0; i < section_index; i++ , it++);
      *address = it->first;
      *len = it->second;
      section_index++;
      return 1;
    } else return 0;
}

extern "C" void read_section_void (long long address, void* buffer, uint64_t size = 0) {
    // check that the address points to a section
    assert(mems.count(address) > 0);
    // copy array
    auto it = mems.find(address);

    if (it == mems.end())
        return;

    memif->read(address, (size == 0) ? sections[address] : size , buffer);
}

extern "C" void read_section_sv (long long address, const svOpenArrayHandle buffer) {
    // get actual poitner
    void* buf = svGetArrayPtr(buffer);
    // check that the address points to a section
    assert(mems.count(address) > 0);

    int i = 0;
    for (auto &datum : mems.find(address)->second) {
      *((char *) buf + i) = datum;
      i++;
    }
}

extern "C" char read_symbol (const char* symbol_name, long long* address) {
    std::string symbol_str(symbol_name);
    auto it = symbols.find(symbol_name);
    if (it != symbols.end()) {
        *address = it->second;
        return 0;
    }
    return 1;
}

extern "C" void read_elf(const char* filename) {
    loaded_binary = filename;

    htif = new htif_hexwriter_t(0x0, 1, -1);

    entry = new reg_t;

    memif = new dpi_memif_t((htif_t*) htif);

    symbols = load_elf(filename, memif, entry);
}
