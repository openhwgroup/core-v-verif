#include "yaml-cpp/yaml.h"
#include "Params.h"

namespace openhw {

    class YamlParamSetter {
        private:
            Params* params;
            std::string yamlFilePath;
        public:
            YamlParamSetter(Params* params, std::string yamlFilePath);
            void setParams();
        private:
            YAML::Node loadConfigFile();
            void setSimulationParameters(YAML::Node config, std::string base, std::string paramBase);
            void redefineParameter(std::string base, std::string paramBase, YAML::const_iterator paramIterator);
    };
}
