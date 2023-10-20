#include <iostream>
#include <string>
#include <unordered_map>
#include <any>
#include <iostream>
#include <stdexcept>

#pragma once

using namespace std;

namespace openhw
{
    typedef struct {
        string base;
        string name;
        any a;
        string description;
    } Param;

    class Params {
        public:
        //              Base                 Name
        unordered_map<string, unordered_map<string, Param>> v;

        any operator[](string str) {
            return this->get(str).a;
        }

        void set(string base, string name, any value, string description="")
        {
            Param p = {base, name, value, description};
            v[base][name] = p;
        }

        void set(string base, string name, Param& p)
        {
            v[base][name] = p;
        }

        Param get(string base, string name)
        {
            auto it = v.find(base);
            if (it != this->v.end())
            {
                auto it2 = it->second.find(name);
                if (it2 != it->second.end())
                    return v[base][name];
                throw std::invalid_argument("The param does not exist");
            }
            return Param();
        }

        Param get(string str)
        {
            string base, name;
            std::size_t n_base = str.find_last_of("/");
            if (n_base != std::string::npos)
            {
                base = str.substr(0, n_base + 1);
                name = str.substr(n_base + 1, str.length());
                return this->get(base, name);
            }
            return Param();

        }

    };

    void ParseParams(string base, Params& baseParams, Params& newParams);
}
