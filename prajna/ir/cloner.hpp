#pragma once

#include <list>
#include <memory>
#include <unordered_map>

// #include "prajna/ir/value.hpp"

namespace prajna::ir {

class Value;
class Function;
class Module;

class FunctionCloner {
   private:
    FunctionCloner() = default;

   public:
    static std::shared_ptr<ir::FunctionCloner> create(std::shared_ptr<ir::Module> ir_module) {
        std::shared_ptr<ir::FunctionCloner> self(new FunctionCloner);
        self->module = ir_module;
        return self;
    }

    std::shared_ptr<ir::Module> module;
    std::list<std::shared_ptr<ir::Function>> functions;
    std::unordered_map<std::shared_ptr<ir::Value>, std::shared_ptr<ir::Value>> value_dict;
};

}  // namespace prajna::ir
