
#include <functional>
#include <iostream>

namespace prajna {

std::function<void(const char *)> print_callback = [](const char *c_str) {
    std::cout << std::string(c_str);
};

}  // namespace prajna
