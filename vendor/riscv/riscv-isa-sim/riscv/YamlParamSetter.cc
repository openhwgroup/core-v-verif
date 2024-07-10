#include "YamlParamSetter.h"

namespace openhw {
    YamlParamSetter::YamlParamSetter(Params* params, std::string yamlFilePath) {
        this->params = params;
        this->yamlFilePath = yamlFilePath;
    }

    void YamlParamSetter::setParams() {
        YAML::Node config = this->loadConfigFile();
        this->setSimulationParameters(config["spike_param_tree"], "/top/", "/top/");

        for(size_t i = 0; i < config["spike_param_tree"]["core_configs"].size(); i++){
            this->setSimulationParameters(config["spike_param_tree"]["core_configs"][i], "/top/cores/", "/top/core/" + std::to_string(i) + "/");
        }
    }

    YAML::Node YamlParamSetter::loadConfigFile() {
        try{
            YAML::Node config = YAML::LoadFile(this->yamlFilePath);
            std::cerr << "[SPIKE] Successfully parsed config file" << endl;
            return config;
        } catch(exception& e) {
            std::cerr << "[SPIKE] Loading config file failed... : " << e.what() << endl;
            throw;
        }
    }

    void YamlParamSetter::setSimulationParameters(YAML::Node config, std::string base, std::string paramBase) {
        for(YAML::const_iterator it = config.begin(); it != config.end(); ++it) {
            if (it->first.as<std::string>() == "core_configs") continue;
            this->redefineParameter(base, paramBase, it);
        }
    }

    void YamlParamSetter::redefineParameter(std::string base, std::string paramBase, YAML::const_iterator paramIterator) {
        std::string paramName = paramIterator->first.as<std::string>();
        std::string setValue = "";
        Param param = this->params->get(base, paramName);
        if (param.type == "string") {
            std::string stringValue = paramIterator->second.as<std::string>();
            this->params->set_string(paramBase, paramName, stringValue, param.default_value, param.description);
            std::cout << "[OK] " << paramBase + paramName << ": " << stringValue << endl;
        }
        else if (param.type == "bool") {
            bool boolValue = paramIterator->second.as<bool>();
            this->params->set_bool(paramBase, paramName, boolValue, param.default_value, param.description);
            std::cout << "[OK] " << paramBase + paramName << ": " << boolValue << endl;
        }
        else if (param.type == "uint64_t") {
            uint64_t uint64Value = paramIterator->second.as<uint64_t>();
            this->params->set_uint64_t(paramBase, paramName, uint64Value, param.default_value, param.description);
            std::cout << "[OK] " << paramBase + paramName << ": 0x" << std::hex << uint64Value << endl;
        }
    }
}
