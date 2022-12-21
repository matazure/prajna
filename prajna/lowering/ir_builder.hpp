#pragma once

#include <stack>

#include "prajna/ir/ir.hpp"
#include "prajna/lowering/builtin.hpp"
#include "prajna/lowering/expression_lowering_visitor.hpp"
#include "prajna/lowering/symbol_table.hpp"
#include "prajna/lowering/template.hpp"

namespace prajna::lowering {

/// @brief 负责IR在构建过程中一些琐事的工作, 和记录IR的当前Function, Block等,
/// 并将创建的Value等插入其中
class IrBuilder {
   public:
    IrBuilder(std::shared_ptr<SymbolTable> symbol_table, std::shared_ptr<ir::Module> ir_module) {
        current_block = nullptr;
        // current_block = ir::Block::create();
        current_function = nullptr;
        this->module = ir_module;
        this->symbol_table = symbol_table;
    }

    IrBuilder() : IrBuilder(nullptr, nullptr) {}

    std::shared_ptr<ir::Type> getIndexType() { return ir::global_context.index_type; }

    std::shared_ptr<ir::ConstantInt> getIndexConstant(int64_t value) {
        auto ir_value = this->create<ir::ConstantInt>(getIndexType(), value);
        this->insert(ir_value);
        return ir_value;
    }

    std::shared_ptr<ir::StructType> getDim3Type() {
        PRAJNA_ASSERT(symbol_table);

        std::list<Symbol> symbol_template_arguments;
        symbol_template_arguments.push_back(this->getIndexType());
        symbol_template_arguments.push_back(this->getIndexConstant(3));

        auto symbol_array = this->symbol_table->get("Array");
        PRAJNA_VERIFY(symbol_array.type() == typeid(std::shared_ptr<TemplateStruct>),
                      "system libs is bad");
        auto array_template = symbolGet<TemplateStruct>(symbol_array);
        auto ir_dim3_type =
            array_template->getStructInstance(symbol_template_arguments, this->module);
        return ir_dim3_type;
    }

    std::shared_ptr<ir::WriteProperty> setDim3(std::shared_ptr<ir::Value> ir_dim3, int64_t index,
                                               std::shared_ptr<ir::Value> ir_value) {
        PRAJNA_ASSERT(this->isArrayType(ir_dim3->type));
        auto ir_index_property = ir_dim3->type->properties["["];
        PRAJNA_VERIFY(ir_index_property, "Array index property is missing");

        auto ir_dim3_variable_liked = this->variableLikedNormalize(ir_dim3);
        auto ir_array_tmp_this_pointer =
            this->create<ir::GetAddressOfVariableLiked>(ir_dim3_variable_liked);
        auto ir_index = this->getIndexConstant(index);
        auto ir_access_property =
            this->create<ir::AccessProperty>(ir_array_tmp_this_pointer, ir_index_property);
        ir_access_property->arguments({ir_index});
        return this->create<ir::WriteProperty>(ir_value, ir_access_property);
    }

    template <typename _Value, typename... _Args>
    std::shared_ptr<_Value> create(_Args &&...__args) {
        auto ir_value = _Value::create(std::forward<_Args>(__args)...);
        static_assert(std::is_base_of<ir::Value, _Value>::value);
        PRAJNA_ASSERT(current_block);
        this->insert(ir_value);
        return ir_value;
    }

    void insert(std::shared_ptr<ir::Value> ir_value) {
        current_block->insert(this->inserter_iterator, ir_value);
        if (this->create_callback) {
            this->create_callback(ir_value);
        }
    }

    std::shared_ptr<ir::VariableLiked> variableLikedNormalize(std::shared_ptr<ir::Value> ir_value) {
        auto ir_variable_liked = cast<ir::VariableLiked>(ir_value);
        if (ir_variable_liked) {
            return ir_variable_liked;
        } else {
            ir_variable_liked = this->create<ir::LocalVariable>(ir_value->type);
            this->create<ir::WriteVariableLiked>(ir_value, ir_variable_liked);
            return ir_variable_liked;
        }
    }

    std::shared_ptr<ir::Call> callMemberFunction(
        std::shared_ptr<ir::Value> ir_object, std::string member_function,
        std::vector<std::shared_ptr<ir::Value>> ir_arguments) {
        auto ir_variable_liked = this->variableLikedNormalize(ir_object);
        auto ir_this_pointer = this->create<ir::GetAddressOfVariableLiked>(ir_variable_liked);
        ir_arguments.insert(ir_arguments.begin(), ir_this_pointer);
        auto ir_member_function = ir_object->type->member_functions[member_function];
        PRAJNA_ASSERT(ir_member_function);
        return this->create<ir::Call>(ir_member_function, ir_arguments);
    }

    std::shared_ptr<ir::Call> callBinaryOeprator(
        std::shared_ptr<ir::Value> ir_object, std::string binary_operator,
        std::vector<std::shared_ptr<ir::Value>> ir_arguments) {
        auto ir_variable_liked = this->variableLikedNormalize(ir_object);
        auto ir_this_pointer = this->create<ir::GetAddressOfVariableLiked>(ir_variable_liked);
        ir_arguments.insert(ir_arguments.begin(), ir_this_pointer);
        auto ir_member_function = ir_object->type->binary_functions[binary_operator];
        PRAJNA_ASSERT(ir_member_function);
        return this->create<ir::Call>(ir_member_function, ir_arguments);
    }

    bool isArrayType(std::shared_ptr<ir::Type> ir_type) {
        return ir_type->fullname.size() > 13 && ir_type->fullname.substr(0, 13) == "::core::Array";
    }

    void pushSymbolTable() {
        auto symbol_new_table = SymbolTable::create(symbol_table);
        symbol_table = symbol_new_table;
    }

    void popSymbolTable() { symbol_table = symbol_table->parent_symbol_table; }

    void pushBlock() {
        auto ir_new_block = ir::Block::create();
        if (current_block) {
            current_block->values.push_back(ir_new_block);
            ir_new_block->parent_block = current_block;
        }

        current_block = ir_new_block;
        inserter_iterator = current_block->values.end();
    }

    void popBlock() {
        if (current_block) {
            current_block = current_block->parent_block;
            inserter_iterator = current_block->values.end();
        };
    }

    void pushBlock(std::shared_ptr<ir::Block> ir_block) {
        ir_block->parent_block = current_block;
        current_block = ir_block;
        inserter_iterator = current_block->values.end();
    }

    void popBlock(std::shared_ptr<ir::Block> ir_block) {
        PRAJNA_ASSERT(ir_block == current_block);
        current_block = current_block->parent_block;
        inserter_iterator = current_block->values.end();
        ir_block->parent_block = nullptr;
    }

    void pushSymbolTableAndBlock() {
        this->pushSymbolTable();
        this->pushBlock();
    }

    void popSymbolTableAndBlock() {
        this->popSymbolTable();
        this->popBlock();
    }

   public:
    std::shared_ptr<SymbolTable> symbol_table = nullptr;
    std::shared_ptr<ir::Function> current_function = nullptr;
    std::shared_ptr<ir::Module> module = nullptr;

    std::shared_ptr<ir::Type> return_type = nullptr;

    std::stack<std::shared_ptr<ir::Label>> loop_after_label_stack;
    std::stack<std::shared_ptr<ir::Label>> loop_before_label_stack;

    std::shared_ptr<ir::Block> current_block = nullptr;
    ir::Block::iterator inserter_iterator;
    std::function<void(std::shared_ptr<ir::Value>)> create_callback;
};

}  // namespace prajna::lowering
