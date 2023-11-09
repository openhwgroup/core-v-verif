#include "Params.h"

namespace openhw
{
    void ParseParams(string base, Params& baseParams, Params& newParams)
    {

        if (newParams.v.find(base) == newParams.v.end())
            return;

        for (auto it = newParams.v[base].begin(); it != newParams.v[base].end(); it++)
        {
            string name = it->first;
            Param p = it->second;
            baseParams.set(base, name, p);
        }
    }
}
