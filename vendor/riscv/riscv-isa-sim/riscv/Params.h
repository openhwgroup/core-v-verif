#include "cfg.h"
#include <any>
#include <iomanip>
#include <iostream>
#include <regex>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <errno.h>
#include <sstream>
#include <type_traits>

#pragma once

using namespace std;

namespace openhw {
typedef struct {
  string base;
  string name;
  string a_string;
  uint64_t a_uint64_t;
  bool   a_bool;
  string default_value;
  string type;
  string description;
} Param;

typedef std::unordered_map<string, Param> mapParam;

class Params {
public:
  //              Base                 Name
  std::unordered_map<string, mapParam> v;

  Param operator[](string str) const { return this->get(str); }

#if 0
  void set(string base, string name, any value, string type = "",
           string default_value = "", string description = "") {
    Param p = {base, name, value, default_value, type, description};
    v[base][name] = p;
  }
#endif

  void set(string base, string name, Param &p) { v[base][name] = p; }

  void set_string(string base, string name, string value,
		  string default_value = "", string description = "") {
    Param p = { base, name, value, 0, 0, default_value, "string", description };
    v[base][name] = p;
  }

  void set_uint64_t(string base, string name, uint64_t value,
		  string default_value = "", string description = "") {
    Param p = { base, name, "", value, false, default_value, "uint64_t", description };
    v[base][name] = p;
  }

  void set_uint64_t(string base, string name, string strval,
		  string default_value = "", string description = "") {
    uint64_t val;
    istringstream(strval) >> val;
    Param p = { base, name, "", val, false, default_value, "uint64_t", description };
    v[base][name] = p;
  }

  void set_bool(string base, string name, bool value,
		  string default_value = "", string description = "") {
    Param p = { base, name, "", 0, value, default_value, "bool", description };
    v[base][name] = p;
  }

  void set_bool(string base, string name, string strval,
		  string default_value = "", string description = "") {
    bool val;
    istringstream(strval) >> std::boolalpha >> val;
    Param p = { base, name, "", 0, val, default_value, "bool", description };
    v[base][name] = p;
  }

  // Set arbitrary parameter from cmdline expression PATH=VALUE.
  void setFromCmdline(string pathColonTypeEqVal) {
    regex regexp("(.+)/([^/:=]+):?([^=]*)=([^=]+)");
    std::smatch match;

    std::regex_match(pathColonTypeEqVal, match, regexp);
    std::cerr << "Params::setFromCmdLine(): setting parameter '" << match[1].str() << "/" << match[2].str() << "' of type '" << match[3].str() << "' to value '" << match[4].str() << "'\n";
    if (match[3].str() == "uint64_t") {
      // 64-bit unsigned integer.  Use base 0 to support any C-style format.
      errno = 0;
      unsigned long uintval = strtoul(match[4].str().c_str(), NULL, 0);
      std::cerr << "### Using unsigned long uintval = " << uintval << "\n";
      if (errno == 0)
        set_uint64_t(match[1].str() + "/", match[2].str(), uintval, match[3].str());
      else
        std::cerr << "??? conversion of '" << match[4].str() << "' to unsigned int FAILED!\n";
    } else if (match[3].str() == "bool") {
      // Boolean value: convert 0/1 directly as numbers, "true"/"false" as boolalpha
      bool val;
      if (match[4].str() == "0" || match[4].str() == "1")
	istringstream(match[4].str()) >> val;
      else
	istringstream(match[4].str()) >> std::boolalpha >> val;
      std::cerr << "### Using bool val = " << std::boolalpha << val << "\n";
      set_bool(match[1].str() + "/", match[2].str(), val, match[3].str());
    }
    Param parm = get(match[1].str() + "/", match[2].str());

    // Visual debug code...
    if (parm.name == "")
       std::cerr << "** Could not get newly set parameter '" << match[1].str() << "/" << match[2].str() << "' !!!\n";
    else {
      std::cerr << "Params::setFromCmdLine(): managed to set parameter '" << match[1].str() << "/" << match[2].str()
		<< "' of type '" << match[3].str()
		<< "' to value '" ;
      if (parm.type == "string")
	std::cerr << parm.a_string;
      else if (parm.type == "uint64_t")
	std::cerr << parm.a_uint64_t;
      else if (parm.type == "bool")
	std::cerr << std::boolalpha << parm.a_bool;
      else
	std::cerr << "<UNKNOWN_TYPE<" << parm.type << ">>";
      std::cerr << "'\n";
    }
  }

  bool exist(string base, string name) {
    auto it = v.find(base);
    if (it != v.end()) {
      auto it2 = it->second.find(name);
      if (it2 != it->second.end())
        return true;
    }
    return false;
  }

  bool exist(string str) {
    string base, name;
    std::size_t n_base = str.find_last_of("/");
    if (n_base != std::string::npos) {
      base = str.substr(0, n_base + 1);
      name = str.substr(n_base + 1, str.length());
      return this->exist(base, name);
    }
    return false;
  }

  Param get(string base, string name) const {
    auto it = v.find(base);
    if (it != this->v.end()) {
      auto it2 = it->second.find(name);
      if (it2 != it->second.end())
        return it2->second;
    }
    return Param();
  }

  Param get(string str) const {
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

  void dump(void);

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
