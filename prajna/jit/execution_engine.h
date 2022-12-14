
#pragma once

#include <memory>

#include "llvm/ExecutionEngine/JITLink/JITLinkMemoryManager.h"
#include "llvm/ExecutionEngine/Orc/LLJIT.h"

namespace prajna::ir {
class Module;
}

namespace prajna::jit {

class ExecutionEngine {
   public:
    ExecutionEngine();

    size_t getValue(std::string name);

    void addIRModule(std::shared_ptr<ir::Module> ir_module);

    void bindCFunction(void* fun_ptr, std::string mangle_name);

    void catchRuntimeError();

    void bindBuiltinFunction();

   private:
    std::unique_ptr<llvm::orc::LLJIT> _up_lljit;
};

}  // namespace prajna::jit
