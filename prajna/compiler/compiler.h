#pragma once

#include <memory>
#include <string>

#include "prajna/compiler/print_callback.h"

namespace prajna {

namespace lowering {
class SymbolTable;
}

namespace ir {
class Module;
}

namespace jit {
class ExecutionEngine;
}

std::shared_ptr<lowering::SymbolTable> createPrimitiveTypes();

// @brief 负责将般若编译器的各个模块整合到一块, 以及和外界的交互
class Compiler {
   private:
    Compiler() = default;

   public:
    static std::shared_ptr<Compiler> create();

    void compileBuiltinSourceFiles(std::string builtin_sources_dir);

    std::shared_ptr<ir::Module> compileCode(std::string code,
                                            std::shared_ptr<lowering::SymbolTable> symbol_table,
                                            std::string file_name, bool is_interpreter);

    void bindBuiltinFunctions();

    void compileCommandLine(std::string command_line_code);

    size_t getSymbolValue(std::string symbol_name);

    void runTestFunctions();

    /**
     * @brief 编译单个源文件
     * @param[in] prajna_source_dir
     * @param[in]
     */
    void compileFile(std::string prajna_source_dir, std::string prajna_source_file);

   private:
    std::shared_ptr<lowering::SymbolTable> _symbol_table;

   public:
    std::shared_ptr<jit::ExecutionEngine> jit_engine;
    size_t compile_error_count = 0;
};

}  // namespace prajna
