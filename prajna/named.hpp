#pragma once

#include <string>

namespace prajna {

class Named {
   public:
    // 默认值为空, 否则llvm的IR不太好看
    std::string name = "";
    std::string fullname = "";
};

inline std::string concatFullname(std::string base_name, std::string name) {
    return base_name + "::" + name;
}

inline std::string getKernelFunctionAddressName(std::string ir_kernel_function_fullname) {
    return ir_kernel_function_fullname + "::kernel_function_address";
}

inline std::string mangleNvvmName(std::string name) {
    std::string str_re;
    for (auto iter = name.begin(); iter != name.end(); ++iter) {
        switch (*iter) {
            case ':':
                str_re.push_back('_');
                continue;
            case '<':
                str_re.append("_");
                continue;
            case '>':
                str_re.append("_");
            case ',':
                str_re.append("_");
                continue;
        }
        str_re.push_back(*iter);
    }

    return str_re;
}

}  // namespace prajna
