
#pragma once

#include <stdexcept>

#include "boost/variant.hpp"
#include "prajna/assert.hpp"
#include "prajna/ast/ast.hpp"
#include "prajna/exception.hpp"
#include "prajna/helper.hpp"
#include "prajna/ir/ir.hpp"
#include "prajna/logger.hpp"
#include "prajna/lowering/ir_builder.hpp"
#include "prajna/lowering/symbol_table.hpp"
#include "prajna/lowering/template.hpp"

namespace prajna::lowering {

class UndefinedSymbolException : public std::exception {
   public:
    UndefinedSymbolException(ast::IdentifiersResolution ast_identifiers_resolution) {
        this->identifier_path = ast_identifiers_resolution;
    }

    ast::IdentifiersResolution identifier_path;
};

class ExpressionLoweringVisitor {
    ExpressionLoweringVisitor() = default;

   public:
    static std::shared_ptr<ExpressionLoweringVisitor> create(std::shared_ptr<IrBuilder> ir_builder,
                                                             std::shared_ptr<Logger> logger) {
        std::shared_ptr<ExpressionLoweringVisitor> self(new ExpressionLoweringVisitor);
        self->logger = logger;
        self->ir_builder = ir_builder;
        return self;
    };

   public:
    bool isIdentifier(ast::IdentifiersResolution ast_identifiers_resolution) {
        if (ast_identifiers_resolution.is_root) {
            return false;
        }

        if (ast_identifiers_resolution.identifiers.size() != 1) {
            return false;
        }

        auto identifier_with_template_parameters = ast_identifiers_resolution.identifiers.front();
        return !identifier_with_template_parameters.template_arguments;
    }

    bool isIdentifier(
        ast::IdentifierWithTemplateArguments ast_identifier_with_template_parameters) {
        ast::IdentifiersResolution ast_identifiers_resolution;
        ast_identifiers_resolution.identifiers = {ast_identifier_with_template_parameters};
        return this->isIdentifier(ast_identifiers_resolution);
    }

    ast::Identifier getIdentifier(ast::IdentifiersResolution ast_identifiers_resolution) {
        return ast_identifiers_resolution.identifiers.front().identifier;
    }

    ast::Identifier getIdentifier(
        ast::IdentifierWithTemplateArguments ast_identifier_with_template_parameters) {
        ast::IdentifiersResolution ast_identifiers_resolution;
        ast_identifiers_resolution.identifiers = {ast_identifier_with_template_parameters};
        return this->getIdentifier(ast_identifiers_resolution);
    }

    std::shared_ptr<ir::Value> apply(ast::Expression ast_expression) {
        PRAJNA_ASSERT(this);
        return (*this)(ast_expression);
    }

    std::shared_ptr<ir::Value> operator()(ast::Blank) {
        PRAJNA_UNREACHABLE;
        return nullptr;
    }

    std::shared_ptr<ir::Value> operator()(ast::CharLiteral ast_char_literal) {
        return ir_builder->create<ir::ConstantChar>(ast_char_literal.value);
    }

    /// @warning 这里后期返回封装好的string类值, 现在先放回一个 char vector
    std::shared_ptr<ir::Value> operator()(ast::StringLiteral ast_string_literal) {
        // 最后需要补零, 以兼容C的字符串
        auto char_string_size = ast_string_literal.value.size() + 1;
        auto ir_char_string_type = ir::ArrayType::create(ir::CharType::create(), char_string_size);
        std::vector<std::shared_ptr<ir::Constant>> ir_inits(ir_char_string_type->size);
        std::transform(RANGE(ast_string_literal.value), ir_inits.begin(),
                       [=](char value) -> std::shared_ptr<ir::Constant> {
                           return ir_builder->create<ir::ConstantChar>(value);
                       });
        // 末尾补零
        ir_inits.back() = ir_builder->create<ir::ConstantChar>('\0');
        auto ir_c_string_constant =
            ir_builder->create<ir::ConstantArray>(ir_char_string_type, ir_inits);
        auto ir_c_string_variable = ir_builder->variableLikedNormalize(ir_c_string_constant);
        auto ir_constant_zero = ir_builder->getIndexConstant(0);
        auto ir_c_string_index0 =
            ir_builder->create<ir::IndexArray>(ir_c_string_variable, ir_constant_zero);
        auto ir_c_string_address =
            ir_builder->create<ir::GetAddressOfVariableLiked>(ir_c_string_index0);
        ast::IdentifiersResolution ast_identifiers_resolution;
        ast_identifiers_resolution.is_root = ast::Operator("::");
        ast_identifiers_resolution.identifiers.resize(1);
        ast_identifiers_resolution.identifiers.front().identifier = "str";
        auto string_type = cast<ir::StructType>(
            symbolGet<ir::Type>(this->applyIdentifiersResolution(ast_identifiers_resolution)));
        auto ir_string_from_char_pat = string_type->static_functions["from_char_ptr"];

        // 内建函数, 无需动态判断调用是否合法, 若使用错误会触发ir::Call里的断言
        return ir_builder->create<ir::Call>(
            ir_string_from_char_pat, std::vector<std::shared_ptr<ir::Value>>{ir_c_string_address});
    }

    std::shared_ptr<ir::Value> operator()(ast::IntLiteral ast_int_literal) {
        return ir_builder->getIndexConstant(ast_int_literal.value);
    };

    std::shared_ptr<ir::Value> operator()(ast::IntLiteralPostfix ast_int_literal_postfix) {
        // -1表示位数和是否有符号尚未确定
        // TODO需要进一步处理
        std::string postfix = ast_int_literal_postfix.postfix;
        auto value = ast_int_literal_postfix.int_literal.value;
        if (postfix == "i8") {
            auto ir_type = ir::IntType::create(8, true);
            return ir_builder->create<ir::ConstantInt>(ir_type, value);
        }
        if (postfix == "i16") {
            auto ir_type = ir::IntType::create(16, true);
            return ir_builder->create<ir::ConstantInt>(ir_type, value);
        }
        if (postfix == "i32") {
            auto ir_type = ir::IntType::create(32, true);
            return ir_builder->create<ir::ConstantInt>(ir_type, value);
        }
        if (postfix == "i64") {
            auto ir_type = ir::IntType::create(64, true);
            return ir_builder->create<ir::ConstantInt>(ir_type, value);
        }
        if (postfix == "u8") {
            auto ir_type = ir::IntType::create(8, false);
            return ir_builder->create<ir::ConstantInt>(ir_type, value);
        }
        if (postfix == "u16") {
            auto ir_type = ir::IntType::create(16, false);
            return ir_builder->create<ir::ConstantInt>(ir_type, value);
        }
        if (postfix == "u32") {
            auto ir_type = ir::IntType::create(32, false);
            return ir_builder->create<ir::ConstantInt>(ir_type, value);
        }
        if (postfix == "u64") {
            auto ir_type = ir::IntType::create(64, false);
            return ir_builder->create<ir::ConstantInt>(ir_type, value);
        }

        auto ir_float = createFloatLiteralPostfix(postfix, static_cast<double>(value));
        if (ir_float) {
            return ir_float;
        }

        logger->error(fmt::format("{} is invalid number postfix", postfix),
                      ast_int_literal_postfix.postfix);
        return nullptr;
    };

    std::shared_ptr<ir::Value> createFloatLiteralPostfix(std::string postfix, double value) {
        if (postfix == "f16") {
            auto ir_type = ir::FloatType::create(16);
            return ir_builder->create<ir::ConstantFloat>(ir_type, value);
        }
        if (postfix == "f32") {
            auto ir_type = ir::FloatType::create(32);
            return ir_builder->create<ir::ConstantFloat>(ir_type, value);
        }
        if (postfix == "f64") {
            auto ir_type = ir::FloatType::create(64);
            return ir_builder->create<ir::ConstantFloat>(ir_type, value);
        }

        return nullptr;
    }

    std::shared_ptr<ir::Value> operator()(ast::FloatLiteralPostfix ast_float_literal_postfix) {
        std::string postfix = ast_float_literal_postfix.postfix;
        auto value = ast_float_literal_postfix.float_literal.value;

        auto ir_float = createFloatLiteralPostfix(postfix, value);
        if (ir_float) {
            return ir_float;
        } else {
            logger->error(fmt::format("{} is invalid number postfix", postfix),
                          ast_float_literal_postfix.postfix);
            return nullptr;
        }
    };

    std::shared_ptr<ir::Value> operator()(ast::FloatLiteral ast_float_literal) {
        auto ir_float_type = ir::FloatType::create(32);
        return ir_builder->create<ir::ConstantFloat>(ir_float_type, ast_float_literal.value);
    }

    std::shared_ptr<ir::Value> operator()(ast::BoolLiteral ast_bool_literal) {
        return ir_builder->create<ir::ConstantBool>(ast_bool_literal.value);
    }

    std::shared_ptr<ir::Value> operator()(ast::Null /*ast_null*/) {
        return ir_builder->create<ir::ConstantNull>();
    }

    std::shared_ptr<ir::Value> operator()(ast::Identifier ast_identifier) {
        if (!ir_builder->symbol_table->has(ast_identifier)) {
            logger->error(fmt::format("{} not found", ast_identifier), ast_identifier);
        }

        auto symbol = ir_builder->symbol_table->get(ast_identifier);
        if (!symbolIs<ir::Value>(symbol)) {
            PRAJNA_UNREACHABLE;
            logger->error(fmt::format("{} is not a valid value"), ast_identifier);
        }

        return symbolGet<ir::Value>(symbol);
    }

    std::shared_ptr<ir::Value> operator()(ast::Expression ast_expresion) {
        auto ir_lhs = applyOperand(ast_expresion.first);
        ir_lhs->source_location = ast_expresion;
        for (auto optoken_and_rhs : ast_expresion.rest) {
            ir_lhs = applyBinaryOperation(ir_lhs, optoken_and_rhs);
            ir_lhs->source_location = optoken_and_rhs;
        }
        return ir_lhs;
    }

    std::shared_ptr<ir::Value> applyBinaryOperationAccessField(
        std::shared_ptr<ir::Value> ir_lhs, ast::BinaryOperation ast_binary_operation) {
        if (ast_binary_operation.operand.type() != typeid(ast::Identifier)) {
            PRAJNA_UNREACHABLE;
            logger->error("access operand must be a identifier", ast_binary_operation);
        }

        auto ir_type = ir_lhs->type;
        auto ir_variable_liked = ir_builder->variableLikedNormalize(ir_lhs);
        std::string member_name = boost::get<ast::Identifier>(ast_binary_operation.operand);
        if (auto member_function = ir_type->member_functions[member_name]) {
            auto ir_this_pointer =
                ir_builder->create<ir::GetAddressOfVariableLiked>(ir_variable_liked);
            return ir::MemberFunctionWithThisPointer::create(ir_this_pointer, member_function);
        }

        auto iter_field = std::find_if(
            RANGE(ir_type->fields),
            [=](std::shared_ptr<ir::Field> ir_field) { return ir_field->name == member_name; });
        if (iter_field != ir_type->fields.end()) {
            auto ir_field_access =
                ir_builder->create<ir::AccessField>(ir_variable_liked, *iter_field);
            return ir_field_access;
        }

        // 索引property
        if (auto ir_property = ir_type->properties[member_name]) {
            auto ir_this_pointer =
                ir_builder->create<ir::GetAddressOfVariableLiked>(ir_variable_liked);
            return ir_builder->create<ir::AccessProperty>(ir_this_pointer, ir_property);
        }

        logger->error(fmt::format("{} is not a member", member_name), ast_binary_operation.operand);
        return nullptr;
    }

    bool isIndexType(std::shared_ptr<ir::Type> ir_type) {
        if (auto ir_int_type = cast<ir::IntType>(ir_type)) {
            if (ir_int_type->is_signed and ir_int_type->bits == 64) {
                return true;
            }
        }

        return false;
    }
    std::shared_ptr<ir::Value> applyBinaryOperationIndexArray(
        std::shared_ptr<ir::Value> ir_object, ast::BinaryOperation ast_binary_operation) {
        auto ir_variable_liked = ir_builder->variableLikedNormalize(ir_object);
        auto ir_arguments =
            *cast<ir::ValueCollection>(this->applyOperand(ast_binary_operation.operand));
        if (ir_arguments.empty()) {
            logger->error("index should have one argument at least", ast_binary_operation.operand);
        }
        auto ir_index = ir_arguments.front();
        if (not this->isIndexType(ir_index->type)) {
            logger->error(
                fmt::format("the index type must be i64, but it's {}", ir_index->type->fullname),
                ast_binary_operation.operand);
        }
        if (is<ir::ArrayType>(ir_object->type)) {
            if (ir_arguments.size() > 1) {
                logger->error("too many index arguments", ast_binary_operation.operand);
            }
            return ir_builder->create<ir::IndexArray>(ir_variable_liked, ir_index);
        }
        if (is<ir::PointerType>(ir_object->type)) {
            if (ir_arguments.size() > 1) {
                logger->error("too many index arguments", ast_binary_operation.operand);
            }
            return ir_builder->create<ir::IndexPointer>(ir_variable_liked, ir_index);
        }
        if (auto ir_index_property = ir_object->type->properties["["]) {
            if (ir_arguments.size() == 1) {
                if (ir_index->type !=
                    ir_index_property->getter_function->function_type->argument_types.back()) {
                    PRAJNA_TODO;
                }
                auto ir_this_pointer =
                    ir_builder->create<ir::GetAddressOfVariableLiked>(ir_variable_liked);
                auto ir_access_property =
                    ir_builder->create<ir::AccessProperty>(ir_this_pointer, ir_index_property);
                ir_access_property->arguments({ir_index});
                return ir_access_property;
            } else {
                // "[" propert在生成的时候就会被限制
                if (not ir_builder->isArrayType(
                        ir_index_property->getter_function->function_type->argument_types.back())) {
                    logger->error("too many index arguments", ast_binary_operation.operand);
                }

                PRAJNA_ASSERT(ast_binary_operation.operand.type() == typeid(ast::Expressions));
                auto ast_arguments = boost::get<ast::Expressions>(ast_binary_operation.operand);
                auto ir_array_argument = this->applyArray(ast_arguments);

                auto ir_this_pointer =
                    ir_builder->create<ir::GetAddressOfVariableLiked>(ir_variable_liked);
                auto ir_access_property =
                    ir_builder->create<ir::AccessProperty>(ir_this_pointer, ir_index_property);
                ir_access_property->arguments({ir_array_argument});
                return ir_access_property;
            }
        }

        logger->error("the object has not a \"[\" property", ast_binary_operation);

        return nullptr;
    }

    std::shared_ptr<ir::Value> applyBinaryOperationCall(std::shared_ptr<ir::Value> ir_lhs,
                                                        ast::BinaryOperation ast_binary_operaton) {
        auto ir_arguments = *cast<ir::ValueCollection>(applyOperand(ast_binary_operaton.operand));
        PRAJNA_ASSERT(ast_binary_operaton.operand.type() == typeid(ast::Expressions));
        auto ast_expressions = boost::get<ast::Expressions>(ast_binary_operaton.operand);
        if (auto ir_member_function = cast<ir::MemberFunctionWithThisPointer>(ir_lhs)) {
            auto ir_function_type = ir_member_function->function_prototype->function_type;
            if (ir_arguments.size() + 1 != ir_function_type->argument_types.size()) {
                logger->error(
                    fmt::format(
                        "the arguments size is not matched, require {} argument, but give {}",
                        ir_function_type->argument_types.size() - 1, ir_arguments.size()),
                    ast_expressions);
            }
            for (size_t i = 0; i < ir_arguments.size(); ++i) {
                if (ir_arguments[i]->type != ir_function_type->argument_types[i + 1]) {
                    logger->error("the argument type is not matched", ast_expressions[i]);
                }
            }
            ir_arguments.insert(ir_arguments.begin(), ir_member_function->this_pointer);
            return ir_builder->create<ir::Call>(ir_member_function->function_prototype,
                                                ir_arguments);
        }

        if (ir_lhs->isFunction()) {
            auto ir_function_type = ir_lhs->getFunctionType();
            if (ir_arguments.size() != ir_function_type->argument_types.size()) {
                logger->error(
                    fmt::format(
                        "the arguments size is not matched, require {} argument, but give {}",
                        ir_function_type->argument_types.size(), ir_arguments.size()),
                    ast_expressions);
            }
            for (size_t i = 0; i < ir_arguments.size(); ++i) {
                if (ir_arguments[i]->type != ir_function_type->argument_types[i]) {
                    logger->error("the argument type is not matched", ast_expressions[i]);
                }
            }
            return ir_builder->create<ir::Call>(ir_lhs, ir_arguments);
        }

        if (auto ir_access_property = cast<ir::AccessProperty>(ir_lhs)) {
            // getter函数必须存在
            auto ir_getter_function_type =
                ir_access_property->property->getter_function->function_type;
            if (ir_arguments.size() != ir_getter_function_type->argument_types.size() - 1) {
                logger->error(
                    fmt::format("the property arguments size is not matched, require {} argument, "
                                "but give {}",
                                ir_getter_function_type->argument_types.size() - 1,
                                ir_arguments.size()),
                    ast_expressions);
            }
            for (size_t i = 0; i < ir_arguments.size(); ++i) {
                if (ir_arguments[i]->type != ir_getter_function_type->argument_types[i + 1]) {
                    logger->error("the argument type is not matched", ast_expressions[i]);
                }
            }
            // 移除, 在末尾插入, 应为参数应该在属性访问的前面
            ir_access_property->parent_block->values.remove(ir_access_property);
            ir_builder->current_block->values.push_back(ir_access_property);
            ir_access_property->arguments(ir_arguments);
            return ir_access_property;
        }

        logger->error("not a valid callable", ast_binary_operaton);
        return nullptr;
    }

    std::shared_ptr<ir::Value> applyBinaryOperation(std::shared_ptr<ir::Value> ir_lhs,
                                                    ast::BinaryOperation ast_binary_operation) {
        if (ast_binary_operation.operator_ == ast::Operator(".")) {
            return this->applyBinaryOperationAccessField(ir_lhs, ast_binary_operation);
        }
        if (ast_binary_operation.operator_ == ast::Operator("(")) {
            return this->applyBinaryOperationCall(ir_lhs, ast_binary_operation);
        }
        if (ast_binary_operation.operator_ == ast::Operator("[")) {
            return this->applyBinaryOperationIndexArray(ir_lhs, ast_binary_operation);
        } else {
            // 将其余的运算都转换为函数调用
            return this->convertBinaryOperationToCallFunction(ir_lhs, ast_binary_operation);
        }

        PRAJNA_UNREACHABLE;
        return nullptr;
    }

    std::shared_ptr<ir::Value> operator()(ast::Expressions ast_expressions) {
        // 仅用于辅助, 故不加入IR中
        auto ir_values = std::make_shared<ir::ValueCollection>();
        for (auto ast_expresion : ast_expressions) {
            auto ir_value = (*this)(ast_expresion);
            ir_values->push_back(ir_value);
        }
        return ir_values;
    }

    std::shared_ptr<ir::Value> applyUnaryOperatorDereferencePointer(
        std::shared_ptr<ir::Value> ir_operand) {
        return ir_builder->create<ir::DeferencePointer>(ir_operand);
    }

    std::shared_ptr<ir::Value> operator()(ast::Unary ast_unary) {
        auto ir_operand = this->applyOperand(ast_unary.operand);
        if (ast_unary.operator_ == ast::Operator("*")) {
            return this->applyUnaryOperatorDereferencePointer(ir_operand);
        }
        if (ast_unary.operator_ == ast::Operator("&")) {
            auto ir_variable_liked = cast<ir::VariableLiked>(ir_operand);
            if (ir_variable_liked == nullptr) {
                logger->error("only could get the address of a VariableLiked", ast_unary);
            }
            return ir_builder->create<ir::GetAddressOfVariableLiked>(ir_variable_liked);
        }

        auto ir_variable_liked = ir_builder->variableLikedNormalize(ir_operand);
        auto unary_operator_name = ast_unary.operator_.string_token;
        auto ir_function = ir_variable_liked->type->unary_functions[unary_operator_name];
        if (not ir_function) {
            logger->error("unary operator not found", ast_unary.operator_);
        }

        auto ir_this_pointer = ir_builder->create<ir::GetAddressOfVariableLiked>(ir_variable_liked);
        std::vector<std::shared_ptr<ir::Value>> ir_arguemnts(1);
        ir_arguemnts[0] = ir_this_pointer;
        return ir_builder->create<ir::Call>(ir_function, ir_arguemnts);
    }

    std::shared_ptr<ir::Value> operator()(ast::Cast ast_cast) {
        auto ir_type = this->applyType(ast_cast.type);
        if (not is<ir::PointerType>(ir_type)) {
            logger->error("the target type of the cast must be a pointer type", ast_cast.type);
        }
        auto ir_value = this->apply(ast_cast.value);
        if (not is<ir::PointerType>(ir_value->type)) {
            logger->error("the type of the cast operand must be pointer type", ast_cast.value);
        }
        return ir_builder->create<ir::BitCast>(ir_value, ir_type);
    }

    std::shared_ptr<ir::Type> applyType(ast::Type ast_postfix_type) {
        auto symbol_type = this->applyIdentifiersResolution(ast_postfix_type.base_type);

        if (!symbolIs<ir::Type>(symbol_type)) {
            logger->error("the symbol is not a type", ast_postfix_type);
        }
        auto ir_type = symbolGet<ir::Type>(symbol_type);

        // @note 有数组类型后需要再处理一下
        for (auto postfix_operator : ast_postfix_type.postfix_type_operators) {
            boost::apply_visitor(
                overloaded{[&ir_type](ast::Operator ast_star) {
                               // parser 处理了
                               PRAJNA_ASSERT(ast_star == ast::Operator("*"));
                               ir_type = ir::PointerType::create(ir_type);
                           },
                           [&ir_type](ast::IntLiteral ast_int_literal) {
                               ir_type = ir::ArrayType::create(ir_type, ast_int_literal.value);
                           },
                           [&ir_type, ir_builder = ir_builder](ast::Identifier ast_identifier) {
                               auto symbol_const_int =
                                   ir_builder->symbol_table->get(ast_identifier);
                               auto ir_constant_int = symbolGet<ir::ConstantInt>(symbol_const_int);
                               // parser 处理了
                               PRAJNA_ASSERT(ir_constant_int);
                               ir_type = ir::ArrayType::create(ir_type, ir_constant_int->value);
                           }},
                postfix_operator);
        }

        return ir_type;
    }  // namespace prajna::lowering

    Symbol applyIdentifiersResolution(ast::IdentifiersResolution ast_identifiers_resolution) {
        Symbol symbol;
        if (ast_identifiers_resolution.is_root) {
            symbol = ir_builder->symbol_table->rootSymbolTable();
        } else {
            symbol = ir_builder->symbol_table;
        }

        // 不应该存在
        PRAJNA_ASSERT(symbol.which() != 0);

        for (auto iter_ast_identifier = ast_identifiers_resolution.identifiers.begin();
             iter_ast_identifier != ast_identifiers_resolution.identifiers.end();
             ++iter_ast_identifier) {
            symbol = boost::apply_visitor(
                overloaded{
                    [=](auto x) -> Symbol {
                        PRAJNA_UNREACHABLE;
                        return nullptr;
                    },
                    [=](std::shared_ptr<ir::Value> ir_value) -> Symbol {
                        logger->error("not a valid scope access", *iter_ast_identifier);
                        return nullptr;
                    },
                    [=](std::shared_ptr<ir::Type> ir_type) -> Symbol {
                        auto static_function_identifier = iter_ast_identifier->identifier;
                        auto ir_static_fun = ir_type->static_functions[static_function_identifier];
                        if (ir_static_fun == nullptr) {
                            logger->error(fmt::format("the static function {} is not exit",
                                                      static_function_identifier),
                                          static_function_identifier);
                        }

                        if (iter_ast_identifier->template_arguments) {
                            logger->error("the template arguments is invalid",
                                          *iter_ast_identifier);
                        }
                        return ir_static_fun;
                    },
                    [=](std::shared_ptr<TemplateStruct> template_strcut) -> Symbol {
                        PRAJNA_UNREACHABLE;
                        return nullptr;
                    },
                    [=](std::shared_ptr<SymbolTable> symbol_table) -> Symbol {
                        auto symbol = symbol_table->get(iter_ast_identifier->identifier);
                        if (symbol.which() == 0) {
                            logger->error("the symbol is not found",
                                          iter_ast_identifier->identifier);
                        }

                        if (!iter_ast_identifier->template_arguments) {
                            return symbol;
                        } else {
                            auto template_struct = symbolGet<TemplateStruct>(symbol);
                            if (template_struct == nullptr) {
                                logger->error(
                                    "it's not a template struct but with template arguments",
                                    *iter_ast_identifier);
                            }
                            std::list<Symbol> symbol_template_arguments;
                            for (auto ast_template_argument :
                                 *iter_ast_identifier->template_arguments) {
                                auto symbol_template_argument = boost::apply_visitor(
                                    overloaded{[=](ast::Blank) -> Symbol {
                                                   PRAJNA_UNREACHABLE;
                                                   return nullptr;
                                               },
                                               [=](ast::Type ast_type) -> Symbol {
                                                   if (ast_type.postfix_type_operators.size() ==
                                                       0) {
                                                       return this->applyIdentifiersResolution(
                                                           ast_type.base_type);
                                                   } else {
                                                       return this->applyType(ast_type);
                                                   }
                                               },
                                               [=](ast::IntLiteral ast_int_literal) -> Symbol {
                                                   return ir::ConstantInt::create(
                                                       ir::global_context.index_type,
                                                       ast_int_literal.value);
                                               }},
                                    ast_template_argument);
                                symbol_template_arguments.push_back(symbol_template_argument);
                            }
                            if (template_struct->template_parameter_identifier_list.size() !=
                                symbol_template_arguments.size()) {
                                logger->error("the template arguments size are not matched",
                                              *iter_ast_identifier->template_arguments);
                            }
                            auto ir_template_type = template_struct->getStructInstance(
                                symbol_template_arguments, ir_builder->module);
                            // 错误应该在之前特化的时候就被拦截, 不会到达这里, 故断言
                            PRAJNA_ASSERT(ir_template_type);
                            return ir_template_type;
                        }
                    }},
                symbol);

            PRAJNA_ASSERT(symbol.which() != 0);
        }

        return symbol;
    }

    std::shared_ptr<ir::Value> operator()(ast::IdentifiersResolution ast_identifiers_resolution) {
        auto symbol = this->applyIdentifiersResolution(ast_identifiers_resolution);
        PRAJNA_ASSERT(symbol.which() != 0);
        return boost::apply_visitor(
            overloaded{
                [](std::shared_ptr<ir::Value> ir_value) -> std::shared_ptr<ir::Value> {
                    return ir_value;
                },
                [=](std::shared_ptr<ir::Type> ir_type) -> std::shared_ptr<ir::Value> {
                    if (ir_type->constructor == nullptr) {
                        logger->error(fmt::format("{} has no constructor", ir_type->fullname),
                                      ast_identifiers_resolution);
                    }
                    return ir_type->constructor;
                },
                [ir_builder = this->ir_builder](std::shared_ptr<ir::ConstantInt> ir_constant_int)
                    -> std::shared_ptr<ir::Value> {
                    // 需要在block里插入, 这才符合后面IR转换生成的规则
                    PRAJNA_ASSERT(ir_constant_int->type == ir_builder->getIndexType());
                    return ir_builder->getIndexConstant(ir_constant_int->value);
                },
                [=](auto x) {
                    logger->error(fmt::format("use invalid symbol as a value"),
                                  ast_identifiers_resolution);
                    return nullptr;
                }},
            symbol);
    }

    // std::shared_ptr<ir::Value> operator()(ast::Array ast_array) {
    //     PRAJNA_ASSERT(ast_array.values.size() > 0);
    //     auto ir_first_value = this->applyOperand(ast_array.values.front());
    //     auto ir_value_type = ir_first_value->type;
    //     auto ir_array = ir_builder->create<ir::LocalVariable>(
    //         ir::ArrayType::create(ir_value_type, ast_array.values.size()));
    //     for (size_t i = 0; i < ast_array.values.size(); ++i) {
    //         auto ir_idx = ir_builder->getIndexConstant(i);
    //         auto ir_index_array = ir_builder->create<ir::IndexArray>(ir_array, ir_idx);
    //         auto ir_value = this->applyOperand(ast_array.values[i]);
    //         if (ir_value->type != ir_value_type) {
    //             logger->error("the array element type are not the same", ast_array.values[i]);
    //         }
    //         ir_builder->create<ir::WriteVariableLiked>(ir_value, ir_index_array);
    //     }

    //     return ir_array;
    // }

    std::shared_ptr<ir::Value> applyArray(std::vector<ast::Expression> ast_array_values) {
        // 获取数组类型
        PRAJNA_ASSERT(ast_array_values.size() > 0);
        auto ir_first_value = this->applyOperand(ast_array_values.front());
        auto ir_value_type = ir_first_value->type;
        std::list<Symbol> symbol_template_arguments;
        symbol_template_arguments.push_back(ir_value_type);
        symbol_template_arguments.push_back(ir_builder->getIndexConstant(ast_array_values.size()));

        auto symbol_array = ir_builder->symbol_table->get("Array");
        PRAJNA_VERIFY(symbol_array.type() == typeid(std::shared_ptr<TemplateStruct>),
                      "system libs is bad");
        auto array_template = symbolGet<TemplateStruct>(symbol_array);
        auto ir_array_type =
            array_template->getStructInstance(symbol_template_arguments, ir_builder->module);

        auto ir_array_tmp = ir_builder->create<ir::LocalVariable>(ir_array_type);
        auto ir_index_property = ir_array_type->properties["["];
        PRAJNA_VERIFY(ir_index_property, "Array index property is missing");
        for (size_t i = 0; i < ast_array_values.size(); ++i) {
            auto ir_value = this->applyOperand(ast_array_values[i]);
            if (ir_value->type != ir_value_type) {
                logger->error("the array element type are not the same", ast_array_values[i]);
            }
            auto ir_index = ir_builder->getIndexConstant(i);
            auto ir_array_tmp_this_pointer =
                ir_builder->create<ir::GetAddressOfVariableLiked>(ir_array_tmp);
            auto ir_access_property = ir_builder->create<ir::AccessProperty>(
                ir_array_tmp_this_pointer, ir_index_property);
            ir_access_property->arguments({ir_index});
            ir_builder->create<ir::WriteProperty>(ir_value, ir_access_property);
        }

        return ir_array_tmp;
    }

    std::shared_ptr<ir::Value> operator()(ast::Array ast_array) {
        return applyArray(ast_array.values);
    }

    std::shared_ptr<ir::Value> operator()(ast::KernelFunctionCall ast_kernel_function_call) {
        auto ir_function = (*this)(ast_kernel_function_call.kernel_function);
        if (ast_kernel_function_call.operation) {
            // TODO 核函数必须有判断@kernel
            auto ir_function_type = ir_function->getFunctionType();
            if (ir_function_type == nullptr) {
                logger->error("not callable", ast_kernel_function_call.kernel_function);
            }
            auto ir_grid_dim = (*this)(ast_kernel_function_call.operation->grid_dim);
            auto ir_block_dim = (*this)(ast_kernel_function_call.operation->block_dim);
            auto ir_arguments =
                *cast<ir::ValueCollection>((*this)(ast_kernel_function_call.operation->arguments));
            // TODO arguments
            auto ir_dim3_type = ir_builder->getDim3Type();
            if (ir_grid_dim->type != ir_dim3_type) {
                logger->error("the grid dim type must be i64[3]",
                              ast_kernel_function_call.operation->grid_dim);
            }
            if (ir_block_dim->type != ir_dim3_type) {
                logger->error("the block dim type must be i64[3]",
                              ast_kernel_function_call.operation->block_dim);
            }

            if (ir_arguments.size() != ir_function_type->argument_types.size()) {
                logger->error(
                    fmt::format(
                        "the arguments size is not matched, require {} argument, but give {}",
                        ir_function_type->argument_types.size(), ir_arguments.size()),
                    ast_kernel_function_call.operation->arguments);
            }
            for (size_t i = 0; i < ir_arguments.size(); ++i) {
                if (ir_arguments[i]->type != ir_function_type->argument_types[i]) {
                    logger->error("the argument type is not matched",
                                  ast_kernel_function_call.operation->arguments[i]);
                }
            }

            return ir_builder->create<ir::KernelFunctionCall>(ir_function, ir_grid_dim,
                                                              ir_block_dim, ir_arguments);

        } else {
            return ir_function;
        }

        PRAJNA_UNREACHABLE;
        return nullptr;
    }

    template <typename _Ast>
    std::shared_ptr<ir::Value> operator()(_Ast ast_operand) {
        PRAJNA_ASSERT(false, typeid(ast_operand).name());
        return nullptr;
    }

    std::shared_ptr<ir::Value> applyOperand(ast::Operand ast_operand) {
        PRAJNA_ASSERT(this);
        return boost::apply_visitor(*this, ast_operand);
    }

    std::shared_ptr<ir::Value> convertBinaryOperationToCallFunction(
        std::shared_ptr<ir::Value> ir_lhs, ast::BinaryOperation ast_binary_operation) {
        // 会把binary operator转换为成员函数的调用
        auto ir_variable_liked = ir_builder->variableLikedNormalize(ir_lhs);
        auto binary_operator_name = ast_binary_operation.operator_.string_token;
        auto ir_function = ir_variable_liked->type->binary_functions[binary_operator_name];
        if (not ir_function) {
            logger->error(
                fmt::format("{} operator not found", ast_binary_operation.operator_.string_token),
                ast_binary_operation.operator_);
        }
        auto ir_this_pointer = ir_builder->create<ir::GetAddressOfVariableLiked>(ir_variable_liked);
        std::vector<std::shared_ptr<ir::Value>> ir_arguemnts(2);
        ir_arguemnts[0] = ir_this_pointer;
        ir_arguemnts[1] = this->applyOperand(ast_binary_operation.operand);
        if (ir_arguemnts[1]->type != ir_function->function_type->argument_types[1]) {
            logger->error(
                fmt::format("the type {} is not matched", ir_arguemnts[1]->type->fullname),
                ast_binary_operation.operand);
        }
        return ir_builder->create<ir::Call>(ir_function, ir_arguemnts);
    }

    std::shared_ptr<ir::Value> operator()(ast::SizeOf ast_sizeof) {
        auto ir_type = this->applyType(ast_sizeof.type);
        return ir_builder->getIndexConstant(ir_type->bytes);
    }

   private:
    std::shared_ptr<IrBuilder> ir_builder;
    std::shared_ptr<Logger> logger;
};

}  // namespace prajna::lowering
