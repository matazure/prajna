#pragma once

#include "prajna/lowering/statement_lowering_visitor.hpp"

namespace prajna::lowering {

class InterpreterLoweringVisitor {
    InterpreterLoweringVisitor() = default;

   public:
    static std::shared_ptr<InterpreterLoweringVisitor> create(
        std::shared_ptr<lowering::SymbolTable> symbol_table, std::shared_ptr<Logger> logger) {
        std::shared_ptr<InterpreterLoweringVisitor> self(new InterpreterLoweringVisitor);
        self->logger = logger;
        self->_statement_lowering_visitor = StatementLoweringVisitor::create(symbol_table, logger);
        return self;
    }

    void operator()(const ast::Statement& x) { boost::apply_visitor(*this, x); }

    void operator()(ast::Statements const& x) {
        for (auto stat : x) {
            (*this)(stat);
        }
    }

    std::shared_ptr<ir::Module> apply(std::shared_ptr<ast::Statements> sp_ast_statements) {
        (*this)(*sp_ast_statements);
        return _statement_lowering_visitor->ir_builder->module;
    }

    std::unique_ptr<function_guard> wrapCommandLineWithFunction() {
        auto ir_fun_type = ir::FunctionType::create(ir::VoidType::create(), {});
        auto ir_function = ir::Function::create(ir_fun_type);
        ir_function->function_type->annotations.insert({"\\command", {}});
        ir_function->name = "\\command" + std::to_string(_command_id++);
        ir_function->fullname = ir_function->name;
        ir_function->parent_module = _statement_lowering_visitor->ir_builder->module;
        _statement_lowering_visitor->ir_builder->module->functions.push_back(ir_function);

        auto ir_builder = _statement_lowering_visitor->ir_builder;
        auto ir_block = ir::Block::create();
        ir_block->parent_function = ir_function;
        ir_builder->pushBlock(ir_block);
        ir_function->blocks.push_back(ir_block);

        return function_guard::create([=]() {
            // 打印结果
            auto ir_builder = _statement_lowering_visitor->ir_builder;
            boost::apply_visitor(
                overloaded{[=](auto x) {},
                           [=](std::shared_ptr<ir::Value> ir_result_value) {
                               if (not ir_result_value->type) return;
                               if (not ir_result_value->type->member_functions["tostr"]) return;
                               auto ir_result_string =
                                   ir_builder->callMemberFunction(ir_result_value, "tostr", {});
                               ir_builder->callMemberFunction(ir_result_string, "print", {});
                           }},
                _symbol_result);

            ir_builder->create<ir::Return>(ir_builder->create<ir::VoidValue>());
            ir_builder->popBlock(ir_block);
        });
    }

    void operator()(const ast::VariableDeclaration& ast_variable_declaration) {
        auto wrap_function_guard = this->wrapCommandLineWithFunction();
        _symbol_result = (*_statement_lowering_visitor)(ast_variable_declaration, true);
    }

    void operator()(const ast::Blank) { return; }

    void operator()(const ast::Return x) { logger->error("\"return\" not in a function", x); }
    void operator()(const ast::Continue x) { logger->error("\"continue\" not in a loop", x); }
    void operator()(const ast::Break x) { logger->error("\"break\" not in a loop", x); }

    void operator()(const ast::Function x) { (*_statement_lowering_visitor)(x); }
    void operator()(const ast::Struct x) { (*_statement_lowering_visitor)(x); }
    void operator()(const ast::ImplementStruct x) { (*_statement_lowering_visitor)(x); }
    void operator()(const ast::Interface x) { (*_statement_lowering_visitor)(x); }
    void operator()(const ast::ImplementStructForInterface x) { (*_statement_lowering_visitor)(x); }

    template <typename T>
    void operator()(const T& t) {
        auto wrap_function_guard = this->wrapCommandLineWithFunction();
        _symbol_result = (*_statement_lowering_visitor)(t);
    }

   private:
    Symbol _symbol_result = nullptr;
    std::shared_ptr<StatementLoweringVisitor> _statement_lowering_visitor = nullptr;
    static size_t _command_id;
    std::shared_ptr<Logger> logger;
};

}  // namespace prajna::lowering
