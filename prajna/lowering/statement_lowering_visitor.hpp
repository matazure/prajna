#pragma once

#include <algorithm>
#include <boost/range/combine.hpp>

#include "boost/variant.hpp"
#include "prajna/assert.hpp"
#include "prajna/ast/ast.hpp"
#include "prajna/helper.hpp"
#include "prajna/ir/ir.hpp"
#include "prajna/logger.hpp"
#include "prajna/lowering/builtin.hpp"
#include "prajna/lowering/expression_lowering_visitor.hpp"
#include "prajna/lowering/ir_builder.hpp"
#include "prajna/lowering/symbol_table.hpp"
#include "prajna/lowering/template.hpp"

namespace prajna::lowering {

class StatementLoweringVisitor {
    StatementLoweringVisitor() = default;

    using result_type = Symbol;

   public:
    static std::shared_ptr<StatementLoweringVisitor> create(
        std::shared_ptr<lowering::SymbolTable> symbol_table, std::shared_ptr<Logger> logger,
        std::shared_ptr<ir::Module> ir_module = nullptr) {
        std::shared_ptr<StatementLoweringVisitor> self(new StatementLoweringVisitor);
        if (!ir_module) ir_module = ir::Module::create();
        self->ir_builder = std::make_shared<IrBuilder>(symbol_table, ir_module);
        self->logger = logger;
        self->expression_lowering_visitor =
            ExpressionLoweringVisitor::create(self->ir_builder, logger);
        return self;
    }

    std::shared_ptr<ir::Module> apply(std::shared_ptr<ast::Statements> sp_ast_statements) {
        (*this)(*sp_ast_statements);
        ir_builder->module->symbol_table = ir_builder->symbol_table;
        return ir_builder->module;
    }

    Symbol operator()(ast::Statements ast_statements) {
        for (auto ast_statement : ast_statements) {
            boost::apply_visitor(*this, ast_statement);
        }

        return nullptr;
    }

    Symbol operator()(ast::Block block) {
        ir_builder->pushSymbolTableAndBlock();

        (*this)(block.statements);
        auto ir_block = ir_builder->current_block;
        ir_builder->popSymbolTableAndBlock();

        return ir_block;
    }

    Symbol operator()(ast::VariableDeclaration ast_variable_declaration,
                      bool use_global_variable = false) {
        std::shared_ptr<ir::Type> ir_type = nullptr;
        std::shared_ptr<ir::Value> ir_initial_value = nullptr;
        if (ast_variable_declaration.type) {
            ir_type = this->applyType(*ast_variable_declaration.type);
        }
        //确定变量的type
        if (ast_variable_declaration.initialize) {
            ir_initial_value =
                expression_lowering_visitor->apply(*ast_variable_declaration.initialize);

            if (!ir_type) {
                ir_type = ir_initial_value->type;
            } else {
                if (ir_type != ir_initial_value->type) {
                    logger->error(fmt::format("the declaration type is \"{}\", but the initialize "
                                              "value's type is \"{}\"",
                                              ir_type->name, ir_initial_value->type->name),
                                  *ast_variable_declaration.initialize);
                }
            }
        }

        // 类型不确定
        if (!ir_type) {
            logger->error("the declaration type is unsure", ast_variable_declaration);
        }

        std::shared_ptr<ir::VariableLiked> ir_variable_liked;
        if (use_global_variable) {
            auto ir_global_variable = ir::GlobalVariable::create(ir_type);
            ir_global_variable->parent_module = ir_builder->module;
            ir_builder->module->global_variables.push_back(ir_global_variable);
            ir_variable_liked = ir_global_variable;
        } else {
            ir_variable_liked = ir_builder->create<ir::LocalVariable>(ir_type);
        }
        ir_builder->symbol_table->setWithName(ir_variable_liked, ast_variable_declaration.name);

        if (ir_initial_value) {
            auto write_variable =
                ir_builder->create<ir::WriteVariableLiked>(ir_initial_value, ir_variable_liked);
        }

        return ir_variable_liked;
    }

    Symbol operator()(ast::Assignment ast_assignment) {
        // 右值应该先解析
        auto ir_rhs = expression_lowering_visitor->applyOperand(ast_assignment.right);
        auto ir_lhs = expression_lowering_visitor->applyOperand(ast_assignment.left);

        if (auto ir_variable_liked = cast<ir::VariableLiked>(ir_lhs)) {
            if (ir_variable_liked->type != ir_rhs->type) {
                logger->error("the type is not matched", ast_assignment);
            }
            ir_builder->create<ir::WriteVariableLiked>(ir_rhs, ir_variable_liked);
            return ir_lhs;
        }

        if (auto ir_property = cast<ir::AccessProperty>(ir_lhs)) {
            if (not ir_property->property->setter_function) {
                logger->error("the property has not a setter function", ast_assignment.left);
            }
            if (ir_property->property->setter_function->function_type->argument_types.back() !=
                ir_rhs->type) {
                logger->error("the type is not matched", ast_assignment);
            }
            ir_builder->create<ir::WriteProperty>(ir_rhs, ir_property);
            return ir_lhs;
        }

        logger->error("the left side is not writeable", ast_assignment.left);

        return nullptr;
    }

    std::vector<std::shared_ptr<ir::Type>> applyParameters(
        std::vector<ast::Parameter> ast_parameters) {
        std::vector<std::shared_ptr<ir::Type>> types(ast_parameters.size());
        std::transform(RANGE(ast_parameters), types.begin(), [=](ast::Parameter ast_parameter) {
            return this->applyType(ast_parameter.type);
        });

        return types;
    }

    auto applyAnnotations(ast::Annotations ast_annotations) {
        std::map<std::string, std::vector<std::string>> annotations;
        for (auto ast_annotation : ast_annotations) {
            std::vector<std::string> values;
            std::transform(RANGE(ast_annotation.values), std::back_inserter(values),
                           [](ast::StringLiteral string_literal) { return string_literal.value; });
            annotations.insert({ast_annotation.name, values});
        }
        return annotations;
    }

    bool allBranchIsTerminated(std::shared_ptr<ir::Block> ir_block,
                               std::shared_ptr<ir::Type> ir_type) {
        PRAJNA_ASSERT(!is<ir::VoidType>(ir_type));
        auto ir_last_value = ir_block->values.back();
        if (auto ir_return = cast<ir::Return>(ir_last_value)) {
            return ir_return->value() && ir_return->value()->type == ir_type;
        }
        if (auto ir_if = cast<ir::If>(ir_last_value)) {
            auto re = this->allBranchIsTerminated(ir_if->trueBlock(), ir_type) &&
                      this->allBranchIsTerminated(ir_if->falseBlock(), ir_type);
            if (re) {
                // //插入一个Return避免错误
                // auto ir
                auto ir_variable = ir_builder->create<ir::LocalVariable>(ir_type);
                auto ir_return = ir_builder->create<ir::Return>(ir_variable);
                ir_if->parent_block->pushBack(ir_return);
                return true;
            } else {
                return false;
            }
        }
        if (auto ir_block_ = cast<ir::Block>(ir_last_value)) {
            return this->allBranchIsTerminated(ir_block_, ir_type);
        }

        return false;
    }

    std::shared_ptr<ir::Function> applyFunctionHeader(
        ast::FunctionHeader ast_function_header, std::shared_ptr<ir::Type> ir_this_pointer_type) {
        std::shared_ptr<ir::Type> return_type;
        if (ast_function_header.return_type) {
            return_type = applyType(*ast_function_header.return_type);
        } else {
            return_type = ir::VoidType::create();
        }
        auto ir_argument_types = applyParameters(ast_function_header.parameters);
        // 插入this-pointer type
        if (ir_this_pointer_type) {
            ir_argument_types.insert(ir_argument_types.begin(), ir_this_pointer_type);
        }

        auto ir_function_type = ir::FunctionType::create(return_type, ir_argument_types);
        auto ir_function = ir::Function::create(ir_function_type);
        ir_function_type->function = ir_function;
        ir_function->parent_module = ir_builder->module;
        ir_builder->module->functions.push_back(ir_function);

        // TODO interface里需要处理一下
        ir_builder->symbol_table->setWithName(ir_function, ast_function_header.name);
        ir_function_type->name = ir_function->name;
        ir_function_type->fullname = ir_function->fullname;
        ir_function_type->annotations = this->applyAnnotations(ast_function_header.annotations);

        return ir_function;
    }

    Symbol operator()(ast::Function ast_function,
                      std::shared_ptr<ir::Type> ir_this_poiner_type = nullptr) {
        auto ir_function = applyFunctionHeader(ast_function.declaration, ir_this_poiner_type);

        ir_builder->current_function = ir_function;
        // 进入参数域,
        ir_builder->pushSymbolTable();
        ir_builder->return_type = ir_function->function_type->return_type;

        // @note 将function的第一个block作为最上层的block
        auto ir_block = ir::Block::create();
        ir_block->parent_function = ir_function;
        ir_builder->pushBlock(ir_block);
        ir_function->blocks.push_back(ir_block);

        size_t j = 0;
        if (ir_this_poiner_type) {
            // Argument也不会插入的block里
            auto ir_this_pointer = ir_builder->create<ir::Argument>(ir_this_poiner_type);
            ir_function->arguments.push_back(ir_this_pointer);
            ir_builder->symbol_table->setWithName(ir_this_pointer, "this-pointer");
            ++j;
        }
        for (size_t i = 0; i < ast_function.declaration.parameters.size(); ++i, ++j) {
            auto ir_argument_type = ir_function->function_type->argument_types[j];
            auto ir_argument = ir_builder->create<ir::Argument>(ir_argument_type);
            ir_function->arguments.push_back(ir_argument);
            ir_builder->symbol_table->setWithName(ir_argument,
                                                  ast_function.declaration.parameters[i].name);
        }

        if (ast_function.body) {
            if (ir_this_poiner_type) {
                auto ir_this_pointer =
                    symbolGet<ir::Value>(ir_builder->symbol_table->get("this-pointer"));
                auto ir_this = ir_builder->create<ir::ThisWrapper>(ir_this_pointer);
                ir_builder->symbol_table->setWithName(ir_this, "this");
            }

            (*this)(*ast_function.body);

            // TODO 返回型需要进一步处理
            // void返回类型直接补一个Return即可, 让后端去优化冗余的指令
            if (is<ir::VoidType>(ir_function->function_type->return_type)) {
                ir_builder->create<ir::Return>(ir_builder->create<ir::VoidValue>());
            } else {
                if (not this->allBranchIsTerminated(ir_function->blocks.back(),
                                                    ir_function->function_type->return_type)) {
                    logger->error("not all branch have been terminated", ast_function.declaration);
                }
            }

        } else {
            ir_function->is_declaration = true;
        }

        ir_builder->return_type = nullptr;
        ir_builder->popBlock(ir_block);
        ir_builder->popSymbolTable();

        return ir_function;
    }

    Symbol operator()(ast::Return ast_return) {
        std::shared_ptr<ir::Return> ir_return;
        if (ast_return.expr) {
            auto ir_return_value = expression_lowering_visitor->apply(*ast_return.expr);
            ir_return = ir_builder->create<ir::Return>(ir_return_value);
        } else {
            auto ir_void_value = ir_builder->create<ir::VoidValue>();
            ir_return = ir_builder->create<ir::Return>(ir_void_value);
        }

        if (ir_return->type != ir_builder->return_type) {
            logger->error(fmt::format("the type is {} , but then function return type is {}",
                                      ir_return->type->fullname, ir_builder->return_type->fullname),
                          ast_return);
        }

        return ir_return;
    }

    Symbol operator()(ast::If ast_if) {
        auto ir_condition = applyExpression(ast_if.condition);
        auto ir_if =
            ir_builder->create<ir::If>(ir_condition, ir::Block::create(), ir::Block::create());

        ir_builder->pushBlock(ir_if->trueBlock());
        (*this)(ast_if.then);
        ir_builder->popBlock(ir_if->trueBlock());

        ir_builder->pushBlock(ir_if->falseBlock());
        if (ast_if.else_) {
            (*this)(*ast_if.else_);
        }
        ir_builder->popBlock(ir_if->falseBlock());

        return ir_if;
    }

    Symbol operator()(ast::While ast_while) {
        auto ir_loop_before = ir::Label::create();
        ir_builder->loop_before_label_stack.push(ir_loop_before);
        auto ir_loop_after = ir::Label::create();
        ir_builder->loop_after_label_stack.push(ir_loop_after);

        auto ir_condition_block = ir::Block::create();
        ir_builder->pushBlock(ir_condition_block);
        // 把ir_loop_before插入到条件块的开头
        ir_builder->insert(ir_loop_before);
        auto ir_condition = applyExpression(ast_while.condition);
        ir_builder->popBlock(ir_condition_block);

        auto ir_while = ir_builder->create<ir::While>(
            ir_condition, ir_condition_block, ir::Block::create(), ir_loop_before, ir_loop_after);

        ir_builder->pushBlock(ir_while->loopBlock());
        (*this)(ast_while.body);
        ir_builder->popBlock(ir_while->loopBlock());

        ir_builder->loop_before_label_stack.pop();
        ir_builder->insert(ir_builder->loop_after_label_stack.top());
        ir_builder->loop_after_label_stack.pop();

        return ir_while;
    }

    Symbol operator()(ast::For ast_for) {
        auto ir_first = expression_lowering_visitor->apply(ast_for.first);
        auto ir_last = expression_lowering_visitor->apply(ast_for.last);
        auto ir_index = ir_builder->create<ir::LocalVariable>(ir_builder->getIndexType());
        ir_builder->symbol_table->setWithName(ir_index, ast_for.index);
        if (not expression_lowering_visitor->isIndexType(ir_first->type)) {
            logger->error("the index type must be i64", ast_for.first);
        }
        if (not expression_lowering_visitor->isIndexType(ir_last->type)) {
            logger->error("the index type must be i64", ast_for.last);
        }

        auto ir_loop_before = ir::Label::create();
        ir_builder->loop_before_label_stack.push(ir_loop_before);
        auto ir_loop_after = ir::Label::create();
        ir_builder->loop_after_label_stack.push(ir_loop_after);

        auto ir_loop_block = ir::Block::create();
        auto ir_for = ir_builder->create<ir::For>(ir_index, ir_first, ir_last, ir_loop_block,
                                                  ir_loop_before, ir_loop_after);

        ir_builder->pushBlock(ir_for->loopBlock());
        (*this)(ast_for.body);
        ir_builder->popBlock(ir_for->loopBlock());

        for (auto ast_annotation : ast_for.annotations) {
            std::vector<std::string> values;
            std::transform(RANGE(ast_annotation.values), std::back_inserter(values),
                           [](ast::StringLiteral string_literal) { return string_literal.value; });
            ir_for->annotations.insert({ast_annotation.name, values});
        }

        PRAJNA_ASSERT(not ir_for->loopBlock()->parent_block);

        ir_builder->loop_before_label_stack.pop();
        ir_builder->insert(ir_builder->loop_after_label_stack.top());
        ir_builder->loop_after_label_stack.pop();

        return ir_for;
    }

    Symbol operator()(ast::Break ast_break) {
        if (not ir_builder->loop_after_label_stack.size()) {
            logger->error("break is outside of a loop", ast_break);
        }

        return ir_builder->create<ir::JumpBranch>(ir_builder->loop_after_label_stack.top());
    }

    Symbol operator()(ast::Continue ast_continue) {
        if (not ir_builder->loop_before_label_stack.size()) {
            logger->error("continue is outside of a loop", ast_continue);
        }

        return ir_builder->create<ir::JumpBranch>(ir_builder->loop_before_label_stack.top());
    }

    void createStructConstructor(std::shared_ptr<ir::StructType> ir_struct_type) {
        auto ir_fields = ir_struct_type->fields;
        std::vector<std::shared_ptr<ir::Type>> ir_constructor_arg_types(ir_fields.size());
        std::transform(RANGE(ir_fields), ir_constructor_arg_types.begin(),
                       [](auto ir_field) { return ir_field->type; });
        auto ir_constructor_type =
            ir::FunctionType::create(ir_struct_type, ir_constructor_arg_types);
        auto ir_constructor = ir::Function::create(ir_constructor_type);
        ir_constructor_type->function = ir_constructor;
        ir_struct_type->constructor = ir_constructor;
        ir_constructor->name = concatFullname(ir_struct_type->name, "constructor");
        ir_constructor->fullname = ir_constructor->name;
        ir_constructor->parent_module = ir_builder->module;
        ir_constructor->arguments.resize(ir_constructor_type->argument_types.size());
        for (size_t i = 0; i < ir_constructor->arguments.size(); ++i) {
            ir_constructor->arguments[i] =
                ir::Argument::create(ir_constructor_type->argument_types[i]);
        }
        ir_builder->module->functions.push_back(ir_constructor);
        auto ir_block = ir::Block::create();
        ir_block->parent_function = ir_constructor;
        ir_constructor->blocks.push_back(ir_block);
        ir_builder->pushBlock(ir_block);
        auto ir_variable = ir_builder->create<ir::LocalVariable>(ir_struct_type);
        for (size_t i = 0; i < ir_fields.size(); ++i) {
            auto ir_field = ir_fields[i];
            auto ir_access_field = ir_builder->create<ir::AccessField>(ir_variable, ir_field);
            ir_builder->create<ir::WriteVariableLiked>(ir_constructor->arguments[i],
                                                       ir_access_field);
        }
        ir_builder->create<ir::Return>(ir_variable);
        ir_builder->popBlock(ir_block);
    }

    std::shared_ptr<ir::Type> applyType(ast::Type ast_postfix_type) {
        return expression_lowering_visitor->applyType(ast_postfix_type);
    }

    std::shared_ptr<ir::StructType> applyStructWithOutTemplates(
        std::shared_ptr<ir::StructType> ir_struct_type, ast::Struct ast_struct) {
        std::vector<std::shared_ptr<ir::Field>> ir_fields(ast_struct.fields.size());
        for (size_t i = 0; i < ast_struct.fields.size(); ++i) {
            ir_fields[i] = ir::Field::create(ast_struct.fields[i].name,
                                             this->applyType(ast_struct.fields[i].type), i);
        }

        ir_struct_type->fields = ir_fields;
        ir_struct_type->update();
        this->createStructConstructor(ir_struct_type);

        return ir_struct_type;
    }

    std::list<std::string> getTemplateParametersIdentifiers(
        std::list<ast::TemplateParameter> template_parameters) {
        std::set<ast::Identifier> template_parameter_identifier_set;
        std::list<std::string> template_parameter_identifier_list;
        for (auto template_parameter : template_parameters) {
            if (template_parameter_identifier_set.count(template_parameter)) {
                logger->error("the template parameter is defined already", template_parameter);
            }
            template_parameter_identifier_list.push_back(template_parameter);
            template_parameter_identifier_set.insert(template_parameter);
        }

        return template_parameter_identifier_list;
    }

    Symbol operator()(ast::Struct ast_struct) {
        if (ast_struct.template_parameters.empty()) {
            auto ir_struct_type = ir::StructType::create({});
            ir_builder->symbol_table->setWithName(ir_struct_type, ast_struct.name);
            return this->applyStructWithOutTemplates(ir_struct_type, ast_struct);
        } else {
            auto template_parameter_identifier_list =
                getTemplateParametersIdentifiers(ast_struct.template_parameters);

            auto symbol_table = ir_builder->symbol_table;

            auto template_struct = std::make_shared<TemplateStruct>();
            template_struct->template_parameter_identifier_list =
                template_parameter_identifier_list;

            // 外部使用算子, 必须值捕获
            auto template_struct_generator =
                [symbol_table, logger = this->logger, ast_struct,
                 template_parameter_identifier_list, template_struct](
                    std::list<Symbol> symbol_list,
                    std::shared_ptr<ir::Module> ir_module) -> std::shared_ptr<ir::StructType> {
                // 包裹一层名字空间, 避免被污染
                auto templates_symbol_table = SymbolTable::create(symbol_table);
                PRAJNA_ASSERT(template_parameter_identifier_list.size() == symbol_list.size());

                std::string symbol_list_fullname = "<";
                for (auto [identifier, symbol] :
                     boost::combine(template_parameter_identifier_list, symbol_list)) {
                    templates_symbol_table->set(symbol, identifier);
                    symbol_list_fullname.append(symbolGetFullname(symbol));
                    symbol_list_fullname.push_back(',');
                }
                if (symbol_list_fullname.back() == ',') symbol_list_fullname.pop_back();
                symbol_list_fullname.push_back('>');

                auto ir_struct_type = ir::StructType::create({});
                ir_struct_type->name = ast_struct.name + symbol_list_fullname;
                ir_struct_type->fullname =
                    concatFullname(symbol_table->fullname(), ir_struct_type->name);
                // @需要提前把ir_struct_type设置, 这样才能嵌套
                template_struct->struct_type_instance_dict[symbol_list] = ir_struct_type;

                auto statement_lowering_visitor =
                    StatementLoweringVisitor::create(templates_symbol_table, logger, ir_module);
                return statement_lowering_visitor->applyStructWithOutTemplates(ir_struct_type,
                                                                               ast_struct);
            };

            template_struct->template_struct_impl =
                Template<ir::StructType>::create(template_struct_generator);
            // auto template_struct = TemplateStruct::create(template_struct_generator);

            ir_builder->symbol_table->setWithName(template_struct, ast_struct.name);

            return template_struct;
        }
    }

    void processUnaryFunction(std::shared_ptr<ir::Type> ir_type,
                              std::shared_ptr<ir::Function> ir_function,
                              ast::Function ast_function) {
        if (not ir_function->function_type->annotations.count("unary")) return;

        if (ir_function->function_type->argument_types.size() != 1) {
            logger->error("the parameters size of a unary function must be 1",
                          ast_function.declaration.parameters);
        }
        auto unary_annotation = ir_function->function_type->annotations["unary"];
        auto iter_unary_annotation = std::find_if(
            RANGE(ast_function.declaration.annotations),
            [](ast::Annotation ast_annotation) { return ast_annotation.name == "unary"; });
        if (unary_annotation.size() != 1) {
            logger->error("the unary annotation should only have one value to represent operator",
                          *iter_unary_annotation);
        }
        auto operator_token = unary_annotation[0];
        std::set<std::string> unary_operators_set = {"+", "-", "*", "&", "!"};
        if (not unary_operators_set.count(operator_token)) {
            logger->error("not valid unary operator", iter_unary_annotation->values[0]);
        }
        ir_type->unary_functions[operator_token] = ir_function;
    }

    void processBinaryFunction(std::shared_ptr<ir::Type> ir_type,
                               std::shared_ptr<ir::Function> ir_function,
                               ast::Function ast_function) {
        if (not ir_function->function_type->annotations.count("binary")) return;

        if (ir_function->function_type->argument_types.size() != 2) {
            logger->error("the parameters size of a binary function must be 2",
                          ast_function.declaration.parameters);
        }
        auto binary_annotation = ir_function->function_type->annotations["binary"];
        auto iter_binary_annotation = std::find_if(
            RANGE(ast_function.declaration.annotations),
            [](ast::Annotation ast_annotation) { return ast_annotation.name == "binary"; });
        if (binary_annotation.size() != 1) {
            logger->error("the binary annotation should only have one value to represent operator",
                          *iter_binary_annotation);
        }
        auto operator_token = binary_annotation[0];
        std::set<std::string> binary_operators_set = {
            "==", "!=", "<",  "<=", ">", ">=", "+", "-", "*",
            "/",  "%",  "<<", ">>", "&", "|",  "^", "!"};
        if (not binary_operators_set.count(operator_token)) {
            logger->error("not valid binary operator", iter_binary_annotation->values[0]);
        }
        ir_type->binary_functions[operator_token] = ir_function;
    }

    void processInitializeCopyDestroyFunction(std::shared_ptr<ir::Type> ir_type,
                                              std::shared_ptr<ir::Function> ir_function,
                                              ast::Function ast_function) {
        // 处理copy等回调函数
        std::set<std::string> copy_destroy_callback_names = {"initialize", "copy", "destroy"};
        if (not copy_destroy_callback_names.count(ir_function->name)) return;

        if (ir_function->function_type->annotations.count("static") != 0) {
            auto iter_static_annotation = std::find_if(
                RANGE(ast_function.declaration.annotations),
                [](ast::Annotation ast_annotation) { return ast_annotation.name == "static"; });
            logger->error(fmt::format("the {} function can not be static", ir_function->name),
                          *iter_static_annotation);
        }

        if (not is<ir::VoidType>(ir_function->function_type->return_type)) {
            logger->error(
                fmt::format("the {} function return type must be void", ir_function->name),
                *ast_function.declaration.return_type);
        }
        // this pointer argument
        if (ir_function->function_type->argument_types.size() != 1) {
            logger->error(
                fmt::format("the {} function should has no parameters", ir_function->name),
                ast_function.declaration.parameters);
        }

        if (ir_function->name == "initialize") {
            ir_type->initialize_function = ir_function;
        }
        if (ir_function->name == "copy") {
            ir_type->copy_function = ir_function;
        }
        if (ir_function->name == "destroy") {
            ir_type->destroy_function = ir_function;
        }
    }

    bool isPropertyGetterSetterFunctionTypeMatched(
        std::shared_ptr<ir::FunctionType> ir_getter_function_type,
        std::shared_ptr<ir::FunctionType> ir_setter_function_type) {
        if (ir_getter_function_type->argument_types.size() + 1 !=
            ir_setter_function_type->argument_types.size()) {
            return false;
        }

        for (size_t i = 0; i < ir_getter_function_type->argument_types.size(); ++i) {
            if (ir_getter_function_type->argument_types[i] !=
                ir_setter_function_type->argument_types[i]) {
                return false;
            }
        }

        if (ir_getter_function_type->return_type !=
            ir_setter_function_type->argument_types.back()) {
            return false;
        }

        return true;
    }

    void processPropertyFunction(std::shared_ptr<ir::Type> ir_type,
                                 std::shared_ptr<ir::Function> ir_function,
                                 ast::Function ast_function) {
        if (not ir_function->function_type->annotations.count("property")) return;

        auto iter_property_annotation = std::find_if(
            RANGE(ast_function.declaration.annotations),
            [](ast::Annotation ast_annotation) { return ast_annotation.name == "properties"; });
        auto property_annotation = ir_function->function_type->annotations["property"];
        if (property_annotation.size() != 2) {
            logger->error("the property annoation should only have two values",
                          iter_property_annotation->values[0]);
        }

        auto property_name = property_annotation[0];
        auto property_tag = property_annotation[1];
        if (property_tag != "setter" && property_tag != "getter") {
            logger->error("should be setter or getter", iter_property_annotation->values[0]);
        }

        auto ir_setter_function_type = ir_function->function_type;
        if (not ir_type->properties[property_name]) {
            ir_type->properties[property_name] = std::make_shared<ir::Property>();
        }
        auto property = ir_type->properties[property_name];
        if (property_tag == "setter") {
            if (property->setter_function) {
                logger->error("the property setter has defined", *iter_property_annotation);
            }
            if (property->getter_function) {
                if (not isPropertyGetterSetterFunctionTypeMatched(
                        property->getter_function->function_type, ir_function->function_type)) {
                    logger->error("the property setter getter functiontype are not matched",
                                  ast_function.declaration);
                }
            }
            property->setter_function = ir_function;
        } else {
            if (property->getter_function) {
                logger->error("the property getter has defined", *iter_property_annotation);
            }

            if (property->setter_function) {
                if (not isPropertyGetterSetterFunctionTypeMatched(
                        ir_function->function_type, property->setter_function->function_type)) {
                    logger->error("the property setter getter functiontype are not matched",
                                  ast_function.declaration);
                }
            }
            property->getter_function = ir_function;
        }
    }

    void applyImplementStructWithOutTemplates(std::shared_ptr<ir::Type> ir_type,
                                              ast::ImplementStruct ast_implement_struct) {
        ir_builder->pushSymbolTable();
        for (auto ast_function : ast_implement_struct.functions) {
            std::shared_ptr<ir::Function> ir_function = nullptr;
            if (std::none_of(RANGE(ast_function.declaration.annotations),
                             [](auto x) { return x.name == "static"; })) {
                auto ir_this_pointer_type = ir::PointerType::create(ir_type);
                auto symbol_function = (*this)(ast_function, ir_this_pointer_type);
                ir_function = cast<ir::Function>(symbolGet<ir::Value>(symbol_function));
                ir_function->function_type->annotations.insert({"member", {}});
                // TODO需要修复
                // PRAJNA_ASSERT(ir_type->member_functions.count(ir_function->name) == 0);
                ir_type->member_functions[ir_function->name] = ir_function;
                ir_function->fullname = concatFullname(ir_type->fullname, ir_function->name);
            } else {
                if (ast_function.declaration.name == "initialize") {
                    int a = 1 + 3;
                }
                ir_builder->pushSymbolTable();
                ir_builder->symbol_table->name =
                    ir_type->name;  // 插入类的名字, 以便函数名字是正确的
                auto symbol_function = (*this)(ast_function);
                ir_function = cast<ir::Function>(symbolGet<ir::Value>(symbol_function));
                ir_builder->popSymbolTable();
                ir_type->static_functions[ir_function->name] = ir_function;
            }

            this->processUnaryFunction(ir_type, ir_function, ast_function);
            this->processBinaryFunction(ir_type, ir_function, ast_function);
            this->processInitializeCopyDestroyFunction(ir_type, ir_function, ast_function);
            this->processPropertyFunction(ir_type, ir_function, ast_function);
        }

        for (auto [property_name, ir_property] : ir_type->properties) {
            if (not ir_property->getter_function) {
                logger->error(fmt::format("the property { } getter must be defined", property_name),
                              ast_implement_struct.struct_);
            }
        }

        ir_builder->popSymbolTable();
    }

    Symbol operator()(ast::ImplementStruct ast_implement_struct) {
        if (ast_implement_struct.template_paramters.empty()) {
            auto ir_symbol = expression_lowering_visitor->applyIdentifiersResolution(
                ast_implement_struct.struct_);
            auto ir_type = symbolGet<ir::Type>(ir_symbol);
            if (ir_type == nullptr) {
                logger->error("the symbol must be a type", ast_implement_struct.struct_);
            }
            this->applyImplementStructWithOutTemplates(ir_type, ast_implement_struct);

        } else {
            auto template_parameter_identifier_list =
                getTemplateParametersIdentifiers(ast_implement_struct.template_paramters);

            auto ir_symbol = expression_lowering_visitor->applyIdentifiersResolution(
                ast_implement_struct.struct_);
            auto template_struct = symbolGet<TemplateStruct>(ir_symbol);
            if (template_struct == nullptr) {
                logger->error("it's not a template struct but with template parameters",
                              ast_implement_struct.template_paramters);
            }
            if (template_struct->template_parameter_identifier_list.size() !=
                template_parameter_identifier_list.size()) {
                logger->error("the template parameters are not matched",
                              ast_implement_struct.template_paramters);
            }

            auto symbol_table = ir_builder->symbol_table;
            auto template_implement_struct_generator =
                [symbol_table, logger = this->logger, ast_implement_struct, template_struct,
                 template_parameter_identifier_list](std::list<Symbol> symbol_list,
                                                     std::shared_ptr<ir::Module> ir_module) {
                    // 包裹一层名字空间, 避免被污染
                    auto templates_symbol_table = SymbolTable::create(symbol_table);
                    PRAJNA_ASSERT(template_parameter_identifier_list.size() == symbol_list.size());
                    for (auto [identifier, symbol] :
                         boost::combine(template_parameter_identifier_list, symbol_list)) {
                        templates_symbol_table->set(symbol, identifier);
                    }
                    auto statement_lowering_visitor =
                        StatementLoweringVisitor::create(templates_symbol_table, logger, ir_module);
                    auto ir_type = template_struct->struct_type_instance_dict[symbol_list];
                    statement_lowering_visitor->applyImplementStructWithOutTemplates(
                        ir_type, ast_implement_struct);
                    // 仅仅用于标记是否实例化, 没有实际用途
                    return std::shared_ptr<ImplementTag>(new ImplementTag);
                };
            auto template_implement_struct =
                Template<ImplementTag>::create(template_implement_struct_generator);
            template_struct->pushBackImplements(template_implement_struct);
        }

        return nullptr;
    }

    Symbol operator()(ast::Expression ast_expression) {
        return this->applyExpression(ast_expression);
    }

    Symbol applyIdentifiersResolution(ast::IdentifiersResolution ast_identifiers_resolution) {
        return expression_lowering_visitor->applyIdentifiersResolution(ast_identifiers_resolution);
    }

    Symbol operator()(ast::Import ast_import) {
        auto symbol = this->applyIdentifiersResolution(ast_import.identifier_path);
        PRAJNA_ASSERT(symbol.which() != 0);
        PRAJNA_ASSERT(!ast_import.identifier_path.identifiers.empty());
        // setWithName 不能改变symbol的名字
        ir_builder->symbol_table->set(symbol,
                                      ast_import.identifier_path.identifiers.back().identifier);

        if (ast_import.as) {
            ir_builder->symbol_table->set(symbol, *ast_import.as);
        }

        return symbol;
    }

    Symbol operator()(ast::Export ast_export) {
        auto symbol = ir_builder->symbol_table->get(ast_export.identifier);
        if (symbol.which() == 0) {
            logger->error("the symbol is not found", ast_export.identifier);
        }

        auto parent_symbol_table = ir_builder->symbol_table->parent_symbol_table;
        PRAJNA_ASSERT(parent_symbol_table, "不可能为nullptr, 因为文件名本身也是一层名字空间");

        if (parent_symbol_table->currentTableHas(ast_export.identifier)) {
            logger->error("the identifier is exist already", ast_export.identifier);
        }

        parent_symbol_table->set(symbol, ast_export.identifier);

        return symbol;
    }

    Symbol operator()(ast::Pragma ast_pragma) {
        if (ast_pragma.name == "error") {
            std::string msg = ast_pragma.values.size() ? ast_pragma.values.front().value : "";
            logger->error(fmt::format("pragma error: {}", msg), ast_pragma);
            return nullptr;
        }
        if (ast_pragma.name == "warning") {
            std::string msg = ast_pragma.values.size() ? ast_pragma.values.front().value : "";
            logger->warning(fmt::format("pragma error: {}", msg), ast_pragma);
            return nullptr;
        }

        logger->error("the pragma is undefined", ast_pragma);
        return nullptr;
    }

    Symbol operator()(ast::Blank) { return nullptr; }

    template <typename _Statement>
    Symbol operator()(_Statement ast_statement) {
        PRAJNA_ASSERT(false, typeid(ast_statement).name());
        return nullptr;
    }

    std::shared_ptr<ir::Value> applyExpression(ast::Expression ast_expression) {
        return expression_lowering_visitor->apply(ast_expression);
    }

   public:
    std::shared_ptr<ExpressionLoweringVisitor> expression_lowering_visitor = nullptr;
    std::shared_ptr<IrBuilder> ir_builder = nullptr;
    std::shared_ptr<Logger> logger = nullptr;
};

}  // namespace prajna::lowering
