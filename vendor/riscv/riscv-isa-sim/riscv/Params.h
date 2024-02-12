#include "cfg.h"
#include <any>
#include <iomanip>
#include <iostream>
#include <regex>
#include <stdexcept>
#include <string>
#include <unordered_map>

#pragma once

using namespace std;

namespace openhw {
typedef struct {
  string base;
  string name;
  any a;
  string default_value;
  string type;
  string description;
} Param;

typedef std::unordered_map<string, Param> mapParam;

class Params {
public:
  //              Base                 Name
  std::unordered_map<string, mapParam> v;

  std::any operator[](string str) { return this->get(str).a; }

  void set(string base, string name, any value, string type = "",
           string default_value = "", string description = "") {
    Param p = {base, name, value, default_value, type, description};
    v[base][name] = p;
  }

  void set(string base, string name, Param &p) { v[base][name] = p; }

  Param get(string base, string name) {
    auto it = v.find(base);
    if (it != this->v.end()) {
      auto it2 = it->second.find(name);
      if (it2 != it->second.end())
        return v[base][name];
    }
    return Param();
  }

  Param get(string str) {
    string base, name;
    std::size_t n_base = str.find_last_of("/");
    if (n_base != std::string::npos) {
      base = str.substr(0, n_base + 1);
      name = str.substr(n_base + 1, str.length());
      return this->get(base, name);
    }
    return Param();
  }

  mapParam get_base(string base) {
    auto it = v.find(base);
    if (it != v.end())
      return it->second;
    return mapParam();
  }

  static void parse_params(string base, Params &baseParams, Params &newParams);

  static void cfg_to_params(cfg_t &cfg, Params &params);

  void print_table(string param_set);

  std::vector<size_t> get_hartids() {
    std::vector<size_t> mhartids;
    regex regexp("/top/proc/[0-9]+");
    for (auto it : this->v) {
      std::smatch match;
      regex_search(it.first, match, regexp);
      for (size_t i = 0; i < match.size(); i++)
        mhartids.push_back(stoi(match[i].str()));
    }
    return mhartids;
  }
};
} // namespace openhw
