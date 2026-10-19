#include "Params.h"
using namespace std;

namespace openhw {
void Params::parse_params(string base, Params &baseParams, Params &newParams) {

  if (newParams.v.find(base) == newParams.v.end())
    return;

  for (auto it = newParams.v[base].begin(); it != newParams.v[base].end();
       it++) {
    string name = it->first;
    Param p = it->second;
    baseParams.set(base, name, p);
  }
}
void Params::cfg_to_params(cfg_t &cfg, Params &params) {
  params.set_string("/top/", "isa", std::string(cfg.isa()));
  params.set_string("/top/", "priv", std::string(cfg.priv()));
  params.set_uint64_t("/top/", "boot_addr",
             (unsigned long)cfg.start_pc.value_or(0x10000UL));

  params.set_string("/top/core/0/", "isa", std::string(cfg.isa()));
  params.set_string("/top/core/0/", "priv", std::string(cfg.priv()));
  params.set_bool("/top/core/0/", "misaligned", cfg.misaligned);
  params.set_uint64_t("/top/core/0/", "pmpregions", (cfg.pmpregions));
}

void dump_param(Param &p) {
  std::cerr << p.base << p.name << " = (" << p.type << ") " ;
  if (p.type == "string")
    std::cerr << p.a_string;
  else if (p.type == "uint64_t")
    std::cerr << "0x" << std::hex << p.a_uint64_t;
  else if (p.type == "bool")
    std::cerr << (p.a_bool ? "true" : "false");
  else
    std::cerr << "<unsupported_type<" << p.type << ">>";
}

void Params::dump(void) {
  for (auto it_base = v.begin(); it_base != v.end(); it_base++)
    for (auto it_parm = it_base->second.begin(); it_parm != it_base->second.end(); it_parm++) {
      dump_param(it_parm->second);
      std::cerr << std::endl;
    }
}

void print_center(string &str, const size_t line_length) {
  size_t str_length = str.length();
  size_t how_many = (line_length - str_length) / 2;

  for (size_t i = 0; i < how_many; ++i)
    cout << ' ';
  cout << str;
  for (size_t i = 0; i < (line_length - str_length) - how_many; ++i)
    cout << ' ';
}

static size_t name_column = 50;
static size_t type_column = 30;
static size_t default_type_column = 40;
static size_t description_column = 100;
static size_t table_size =
    name_column + type_column + default_type_column + description_column;

void print_param(Param &param) {
  string name = param.base + param.name;
  string type = param.type;
  string default_value = param.default_value;
  string description = param.description;
  cout << '|';
  print_center(name, name_column - 1);
  cout << '|';
  print_center(type, type_column - 1);
  cout << '|';
  print_center(default_value, default_type_column - 1);
  cout << '|';
  print_center(description, description_column - 2);
  cout << '|' << std::endl;
}

void print_row_separator(size_t size) {
  for (size_t i = 0; i < table_size; i++)
    std::cout << '-';
  cout << std::endl;
}

void print_header() {
  print_row_separator(table_size);
  Param table_header = {"Name", "", "", 0, false, "Default", "Type", "Description"};
  print_param(table_header);
  print_row_separator(table_size);
}

void Params::print_table(string param_set) {
  print_header();
  auto it = this->v.find(param_set);

  // Sort unordered_map keys
  std::vector<string> keys;
  for (auto it2 = it->second.begin(); it2 != it->second.end(); ++it2)
    keys.push_back(it2->first);

  sort(keys.begin(), keys.end());

  // Print each param
  for (auto key : keys)
    print_param(it->second[key]);

  print_row_separator(table_size);
}
} // namespace openhw
