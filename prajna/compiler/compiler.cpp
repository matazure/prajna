#include "prajna/compiler/compiler.h"

#include <filesystem>
#include <fstream>

#include "boost/algorithm/string.hpp"
#include "prajna/assert.hpp"
#include "prajna/codegen/llvm_codegen.h"
#include "prajna/exception.hpp"
#include "prajna/jit/execution_engine.h"
#include "prajna/logger.hpp"
#include "prajna/lowering/create_primitive_env.hpp"
#include "prajna/lowering/lower.h"
#include "prajna/parser/parse.h"
#include "prajna/transform/transform.h"

namespace prajna {

namespace fs = std::filesystem;

namespace {

inline std::shared_ptr<lowering::SymbolTable> createSymbolTableTree(
    std::shared_ptr<lowering::SymbolTable> root_symbol_table, std::string prajna_source_file) {
    auto source_file_path_string = fs::path(prajna_source_file).lexically_normal().string();
    std::vector<std::string> result;
    boost::split(result, source_file_path_string, boost::is_any_of("/"));
    result.back() = fs::path(result.back()).stem().string();
    auto symbol_table_tree = root_symbol_table;
    for (auto path_part : result) {
        if (symbol_table_tree->has(path_part)) {
            symbol_table_tree =
                lowering::symbolGet<lowering::SymbolTable>(symbol_table_tree->get(path_part));
        } else {
            auto new_symbol_table = lowering::SymbolTable::create(symbol_table_tree);
            symbol_table_tree->set(new_symbol_table, path_part);
            new_symbol_table->name = path_part;
            symbol_table_tree = new_symbol_table;
        }
    }

    return symbol_table_tree;
}

}  // namespace

std::shared_ptr<Compiler> Compiler::create() {
    std::shared_ptr<Compiler> self(new Compiler);
    self->_symbol_table = lowering::createPrimitiveTypes();
    self->jit_engine = std::make_shared<jit::ExecutionEngine>();
    self->jit_engine->bindBuiltinFunction();
    return self;
}

void Compiler::compileBuiltinSourceFiles(std::string builtin_sources_dir) {
    this->compileFile(builtin_sources_dir, "implement_primitive_types.prajna");
    this->compileFile(builtin_sources_dir, "bindings.prajna");
    this->compileFile(builtin_sources_dir, "core.prajna");
    this->compileFile(builtin_sources_dir, "serialize.prajna");
    this->compileFile(builtin_sources_dir, "testing.prajna");

#ifdef PRAJNA_WITH_GPU
    this->compileFile(builtin_sources_dir, "cuda.prajna");
    this->compileFile(builtin_sources_dir, "gpu.prajna");
#endif
}

std::shared_ptr<ir::Module> Compiler::compileCode(
    std::string code, std::shared_ptr<lowering::SymbolTable> symbol_table, std::string file_name,
    bool is_interpreter) {
    try {
        auto logger = Logger::create(code);
        auto ast = prajna::parser::parse(code, file_name, logger);
        PRAJNA_ASSERT(ast);
        auto ir_lowering_module =
            prajna::lowering::lower(ast, symbol_table, logger, is_interpreter);
        ir_lowering_module->name = file_name;
        ir_lowering_module->fullname = ir_lowering_module->name;
        for (auto [ir_target, ir_sub_module] : ir_lowering_module->modules) {
            if (ir_sub_module == nullptr) continue;
            ir_sub_module->name = ir_lowering_module->name + "_" + ir::targetToString(ir_target);
            ir_sub_module->fullname = ir_sub_module->name;
        }
        auto ir_ssa_module = prajna::transform::transform(ir_lowering_module);
        auto ir_codegen_module = prajna::codegen::llvmCodegen(ir_ssa_module, ir::Target::host);
        jit_engine->addIRModule(ir_codegen_module);

        return ir_lowering_module;
    } catch (CompileError &) {
        ++compile_error_count;
        return nullptr;
    }
}

void Compiler::compileCommandLine(std::string command_line_code) {
    static int command_id = 0;
    auto ir_module = this->compileCode(command_line_code, _symbol_table,
                                       ":cmd" + std::to_string(command_id++), true);
    if (not ir_module) return;

    jit_engine->catchRuntimeError();
    // @note 会有一次输入多个句子的情况
    for (auto ir_function : ir_module->functions) {
        if (ir_function->function_type->annotations.count("\\command")) {
            auto fun_fullname = ir_function->fullname;
            auto fun_ptr = reinterpret_cast<void (*)(void)>(jit_engine->getValue(fun_fullname));
            fun_ptr();
        }
    }
}

void Compiler::runTestFunctions() {
    this->_symbol_table->each([this](lowering::Symbol symbol) {
        if (auto ir_value = lowering::symbolGet<ir::Value>(symbol)) {
            if (auto ir_function = cast<ir::Function>(ir_value)) {
                if (ir_function->function_type->annotations.count("test")) {
                    auto function_pointer = this->jit_engine->getValue(ir_function->fullname);
                    this->jit_engine->catchRuntimeError();
                    reinterpret_cast<void (*)(void)>(function_pointer)();
                }
            }
        }
    });
}

size_t Compiler::getSymbolValue(std::string symbol_name) {
    return this->jit_engine->getValue(symbol_name);
}

void Compiler::compileFile(std::string prajna_source_dir, std::string prajna_source_file) {
    auto prajna_source_full_path =
        fs::current_path() / fs::path(prajna_source_dir) / fs::path(prajna_source_file);
    std::ifstream ifs(prajna_source_full_path);
    PRAJNA_ASSERT(ifs.good());
    std::string code((std::istreambuf_iterator<char>(ifs)), std::istreambuf_iterator<char>());

    auto current_symbol_table = createSymbolTableTree(_symbol_table, prajna_source_file);
    this->compileCode(code, current_symbol_table, prajna_source_full_path, false);
}

}  // namespace prajna
