#pragma once

#include <list>
#include <map>
#include <set>

#include "prajna/ir/ir.hpp"
#include "prajna/logger.hpp"
#include "prajna/lowering/statement_lowering_visitor.hpp"
#include "prajna/parser/parse.h"
#include "prajna/transform/transform_pass.hpp"
#include "prajna/transform/utility.hpp"

namespace prajna::transform {

/// @note 删除的节点需要调用finilize函数, 以避免循环依赖导致的内存泄露
/// @note 当遍历某个操作时, 先拷贝一下, 除非确定没有插入删除操作

class FlatternBlockPass : public FunctionPass {
   public:
    bool flatternBlock(std::shared_ptr<ir::Block> ir_block) {
        bool changed = false;
        for (auto iter = ir_block->values.begin(); iter != ir_block->values.end();) {
            if (auto ir_cur_block = cast<ir::Block>(*iter)) {
                PRAJNA_ASSERT(!is<ir::Label>(ir_cur_block));

                this->flatternBlock(ir_cur_block);

                for (auto ir_value : ir_cur_block->values) {
                    ir_block->insert(iter, ir_value);
                }
                iter = ir_block->values.erase(iter);
                ir_cur_block->finalize();
                changed = true;
                continue;
            }
            if (auto ir_if = cast<ir::If>(*iter)) {
                this->flatternBlock(ir_if->trueBlock());
                this->flatternBlock(ir_if->falseBlock());

                auto ir_true_label = ir::Label::create();
                auto ir_false_label = ir::Label::create();
                ir_if->trueBlock()->pushFront(ir_true_label);
                ir_if->falseBlock()->pushFront(ir_false_label);
                auto ir_condition_branch =
                    ir::ConditionBranch::create(ir_if->condition(), ir_true_label, ir_false_label);

                auto ir_end_merge_label = ir::Label::create();
                auto ir_true_branch = ir::JumpBranch::create(ir_end_merge_label);
                ir_if->trueBlock()->pushBack(ir_true_branch);
                auto ir_false_branch = ir::JumpBranch::create(ir_end_merge_label);
                ir_if->falseBlock()->pushBack(ir_false_branch);

                ir_block->insert(iter, ir_condition_branch);
                for (auto e : ir_if->trueBlock()->values) {
                    ir_block->insert(iter, e);
                }
                for (auto e : ir_if->falseBlock()->values) {
                    ir_block->insert(iter, e);
                }
                ir_block->insert(iter, ir_end_merge_label);

                iter = ir_block->values.erase(iter);
                // ir_if, ir_if->true/falseBlock()会有循环依赖, 需要强制析构
                ir_if->trueBlock()->finalize();   // 非必须
                ir_if->falseBlock()->finalize();  // 非必须
                ir_if->finalize();                // 必须的

                changed = true;
                continue;
            }
            if (auto ir_while = cast<ir::While>(*iter)) {
                this->flatternBlock(ir_while->loopBlock());

                auto ir_label_loop = ir::Label::create();
                ir_while->loopBlock()->pushFront(ir_label_loop);
                auto ir_label_after_loop = ir::Label::create();
                auto ir_condition_branch = ir::ConditionBranch::create(
                    ir_while->condition(), ir_label_loop, ir_label_after_loop);
                ir_while->conditionBlock()->pushBack(ir_condition_branch);

                auto ir_label_condition_entry = ir::Label::create();
                ir_while->conditionBlock()->pushFront(ir_label_condition_entry);
                auto ir_jump_branch = ir::JumpBranch::create(ir_label_condition_entry);
                ir_while->loopBlock()->pushBack(ir_jump_branch);

                //在while开始的地方, 需要jump到conditionBlock(),
                auto ir_concat_branch = ir::JumpBranch::create(ir_label_condition_entry);
                ir_block->insert(iter, ir_concat_branch);
                for (auto e : ir_while->conditionBlock()->values) {
                    ir_block->insert(iter, e);
                }
                for (auto e : ir_while->loopBlock()->values) {
                    ir_block->insert(iter, e);
                }
                ir_block->insert(iter, ir_label_after_loop);

                iter = ir_block->values.erase(iter);
                // 会有循环依赖, 必须强制析构
                ir_while->conditionBlock()->finalize();
                ir_while->loopBlock()->finalize();
                ir_while->finalize();

                changed = true;
                continue;
            }
            if (auto ir_for = cast<ir::For>(*iter)) {
                // 即使标注了gpu, 其内部也应该展开以便简化后续的分析流程
                this->flatternBlock(ir_for->loopBlock());

                // 标注gpu的则在后面抽离,
                if (ir_for->annotations.count("gpu")) {
                    ++iter;
                    continue;
                }

                auto ir_builder = std::make_shared<lowering::IrBuilder>();
                ir_builder->current_block = ir_block;
                ir_builder->inserter_iterator = iter;

                auto ir_write_first =
                    ir_builder->create<ir::WriteVariableLiked>(ir_for->first(), ir_for->index());

                auto ir_label_condition_entry = ir::Label::create();
                auto ir_concat_jump = ir_builder->create<ir::JumpBranch>(ir_label_condition_entry);
                ir_block->insert(iter, ir_label_condition_entry);
                auto ir_label_loop = ir::Label::create();
                ir_for->loopBlock()->pushFront(ir_label_loop);
                // insertCallMemmberFunction会插入ir_condition
                auto ir_condition =
                    ir_builder->callBinaryOeprator(ir_for->index(), "<", {ir_for->last()});
                auto ir_label_after_loop = ir::Label::create();
                auto ir_condition_branch = ir_builder->create<ir::ConditionBranch>(
                    ir_condition, ir_label_loop, ir_label_after_loop);

                {
                    std::string code = "i = i + 1;";
                    auto logger = Logger::create(code);
                    auto ast = prajna::parser::parse(code, "//None", logger);
                    auto symbol_table = ir_block->getParentFunction()->parent_module->symbol_table;
                    auto statement_lowering_visitor =
                        lowering::StatementLoweringVisitor::create(symbol_table, logger);
                    auto ir_builder = statement_lowering_visitor->ir_builder;
                    ir_builder->pushSymbolTable();
                    ir_builder->pushBlock(ir_for->loopBlock());
                    ir_builder->symbol_table->set(ir_for->index(), "i");
                    statement_lowering_visitor->apply(ast);
                    ir_builder->popSymbolTable();
                    ir_builder->popBlock(ir_for->loopBlock());
                }

                auto ir_jump_branch = ir::JumpBranch::create(ir_label_condition_entry);
                ir_for->loopBlock()->pushBack(ir_jump_branch);
                for (auto e : ir_for->loopBlock()->values) {
                    ir_block->insert(iter, e);
                }
                ir_block->insert(iter, ir_label_after_loop);
                iter = ir_block->values.erase(iter);

                ir_for->loopBlock()->finalize();
                ir_for->finalize();

                changed = true;
                continue;
            }

            ++iter;
        }

        return changed;
    }

    std::list<std::shared_ptr<ir::Block>> splitBlock(std::shared_ptr<ir::Block> ir_top_block) {
        std::list<std::shared_ptr<ir::Block>> blocks;
        blocks.push_back(ir::Block::create());  // @note 函数开头不能插入ir::Label否则和这里矛盾
        for (auto ir_value : ir_top_block->values) {
            PRAJNA_ASSERT(!is<ir::Block>(ir_value) || is<ir::Label>(ir_value));
            if (auto ir_label = cast<ir::Label>(ir_value)) {
                blocks.push_back(ir::Block::create());

                // ir_label作为操作时修改时(移除或添加), 都会改变instructions_with_index的值,
                // 故应该先拷贝一份
                auto instructions_with_index_copy = ir_label->instruction_with_index_list;
                for (auto inst_with_idx : instructions_with_index_copy) {
                    inst_with_idx.instruction->operand(inst_with_idx.operand_index, blocks.back());
                }
            } else {
                blocks.back()->pushBack(ir_value);
            }
        }

        return blocks;
    }

    bool runOnFunction(std::shared_ptr<ir::Function> ir_function) override {
        auto ir_top_block = ir_function->blocks.front();
        this->flatternBlock(ir_top_block);
        // 分离成标准ssa的block形式
        ir_function->blocks = this->splitBlock(ir_top_block);
        for (auto ir_block : ir_function->blocks) {
            ir_block->parent_function = ir_function;
            ir_block->parent_block = nullptr;
        }

        return true;
    }
};

/// @brief 将变量转换为指针的存取
class ConvertVariableToPointerPass : public FunctionPass {
   public:
    bool insertValueToBlock(std::shared_ptr<ir::Function> ir_function) {
        bool changed = false;
        std::set<std::shared_ptr<ir::Value>> ir_values;
        for (auto ir_block : ir_function->blocks) {
            for (auto iter_ir_value = ir_block->values.begin();
                 iter_ir_value != ir_block->values.end(); ++iter_ir_value) {
                auto ir_value = *iter_ir_value;
                ir_values.insert(ir_value);

                if (auto ir_instruction = cast<ir::Instruction>(ir_value)) {
                    for (auto i = 0; i < ir_instruction->operandSize(); ++i) {
                        auto ir_operand = ir_instruction->operand(i);
                        if (ir_values.count(ir_operand) == 0) {
                            // 模板实例化时会产生非Block的Constant,并且会被使用
                            if (is<ir::ConstantInt>(ir_operand)) {
                                ir_block->insert(iter_ir_value, ir_operand);
                                ir_values.insert(ir_operand);
                                changed = true;
                            }
                        }
                    }
                }
            }
        }

        return changed;
    }

    bool convertThisWrapperToDeferencePointer(std::shared_ptr<ir::Function> ir_function) {
        auto ir_this_wrappers = utility::getValuesInFunction<ir::ThisWrapper>(ir_function);

        // 可能需要重构, 应为"this;"这样的代码无意义, 也许应该取个右值.
        PRAJNA_ASSERT(ir_this_wrappers.size() <= 1, "只可能成员函数开头加入一个");
        for (auto ir_this_wrapper : ir_this_wrappers) {
            // 改变使用它的
            auto instructions_with_index_copy = ir_this_wrapper->instruction_with_index_list;
            for (auto instruction_with_index_list : instructions_with_index_copy) {
                auto ir_inst = instruction_with_index_list.instruction;
                size_t op_idx = instruction_with_index_list.operand_index;
                auto ir_deference_pointer =
                    ir::DeferencePointer::create(ir_this_wrapper->thisPointer());
                auto ir_block = ir_inst->parent_block;
                auto iter = std::find(ir_block->values.begin(), ir_block->values.end(), ir_inst);
                ir_block->insert(iter, ir_deference_pointer);
                ir_inst->operand(op_idx, ir_deference_pointer);
            }

            ir_this_wrapper->parent_block->remove(ir_this_wrapper);
            ir_this_wrapper->finalize();
        }

        return !ir_this_wrappers.empty();
    }

    bool convertVariableToDeferencePointer(std::shared_ptr<ir::Function> ir_function) {
        auto ir_variables = utility::getValuesInFunction<ir::LocalVariable>(ir_function);

        for (auto ir_variable : ir_variables) {
            //改变它自己
            std::shared_ptr<ir::Value> ir_alloca = ir::Alloca::create(ir_variable->type);
            ir_alloca->name = ir_variable->name;
            ir_alloca->fullname = ir_alloca->name;

            // @note ir::Alloca不应该出现在循环体内部, 故直接再将其放在函数的第一个块
            ir_function->blocks.front()->pushFront(ir_alloca);
            ir_variable->parent_block->remove(ir_variable);

            // 改变使用它的
            auto instructions_with_index_copy = ir_variable->instruction_with_index_list;
            for (auto instruction_with_index_list : instructions_with_index_copy) {
                auto ir_inst = instruction_with_index_list.instruction;
                size_t op_idx = instruction_with_index_list.operand_index;

                auto ir_deference_pointer = ir::DeferencePointer::create(ir_alloca);
                auto ir_block = ir_inst->parent_block;
                auto iter = std::find(ir_block->values.begin(), ir_block->values.end(), ir_inst);
                ir_block->insert(iter, ir_deference_pointer);
                ir_inst->operand(op_idx, ir_deference_pointer);
            }

            ir_variable->finalize();
        }

        return !ir_variables.empty();
    }

    bool convertAccessFieldToGetStructElementPointer(std::shared_ptr<ir::Function> ir_function) {
        auto ir_access_fields = utility::getValuesInFunction<ir::AccessField>(ir_function);

        for (auto ir_access_field : ir_access_fields) {
            auto ir_object_deference_ptr = cast<ir::DeferencePointer>(ir_access_field->object());
            PRAJNA_ASSERT(ir_object_deference_ptr);
            auto ir_struct_get_element_ptr = ir::GetStructElementPointer::create(
                ir_object_deference_ptr->pointer(), ir_access_field->field);
            PRAJNA_ASSERT(ir_object_deference_ptr->parent_block,
                          "解指针可能被多次删除, 不符合使用场景");
            ir_object_deference_ptr->parent_block->remove(ir_object_deference_ptr);
            ir_object_deference_ptr->finalize();
            utility::replaceInBlock(ir_access_field, ir_struct_get_element_ptr);

            auto instructions_with_index_copy = ir_access_field->instruction_with_index_list;
            for (auto instruction_with_index_list : instructions_with_index_copy) {
                auto ir_inst = instruction_with_index_list.instruction;
                size_t op_idx = instruction_with_index_list.operand_index;

                auto ir_deference_pointer = ir::DeferencePointer::create(ir_struct_get_element_ptr);
                auto iter_inst = std::find(RANGE(ir_inst->parent_block->values), ir_inst);
                ir_inst->parent_block->insert(iter_inst, ir_deference_pointer);
                ir_inst->operand(op_idx, ir_deference_pointer);
            }

            ir_access_field->finalize();
        }

        return !ir_access_fields.empty();
    }

    bool convertIndexArrayToGetArrayElementPointer(std::shared_ptr<ir::Function> ir_function) {
        auto ir_index_arrays = utility::getValuesInFunction<ir::IndexArray>(ir_function);

        for (auto ir_index_array : ir_index_arrays) {
            auto ir_object_deference_ptr = cast<ir::DeferencePointer>(ir_index_array->object());
            PRAJNA_ASSERT(ir_object_deference_ptr);
            auto ir_array_get_element_ptr = ir::GetArrayElementPointer::create(
                ir_object_deference_ptr->pointer(), ir_index_array->index());
            ir_object_deference_ptr->parent_block->remove(ir_object_deference_ptr);
            ir_object_deference_ptr->finalize();
            utility::replaceInBlock(ir_index_array, ir_array_get_element_ptr);

            auto instructions_with_index_copy = ir_index_array->instruction_with_index_list;
            for (auto instruction_with_index_list : instructions_with_index_copy) {
                auto ir_inst = instruction_with_index_list.instruction;
                size_t op_idx = instruction_with_index_list.operand_index;

                auto ir_deference_pointer = ir::DeferencePointer::create(ir_array_get_element_ptr);
                auto iter_inst = std::find(RANGE(ir_inst->parent_block->values), ir_inst);
                ir_inst->parent_block->insert(iter_inst, ir_deference_pointer);
                ir_inst->operand(op_idx, ir_deference_pointer);
            }

            ir_index_array->finalize();
        }

        return !ir_index_arrays.empty();
    }

    bool convertIndexPointerToGetPointerElementPointer(std::shared_ptr<ir::Function> ir_function) {
        auto ir_index_pointers = utility::getValuesInFunction<ir::IndexPointer>(ir_function);

        for (auto ir_index_pointer : ir_index_pointers) {
            auto ir_object_deference_ptr = cast<ir::DeferencePointer>(ir_index_pointer->object());
            PRAJNA_ASSERT(ir_object_deference_ptr);
            auto ir_pointer_get_element_ptr = ir::GetPointerElementPointer::create(
                ir_object_deference_ptr->pointer(), ir_index_pointer->index());
            ir_object_deference_ptr->parent_block->remove(ir_object_deference_ptr);
            ir_object_deference_ptr->finalize();
            utility::replaceInBlock(ir_index_pointer, ir_pointer_get_element_ptr);

            auto instructions_with_index_copy = ir_index_pointer->instruction_with_index_list;
            for (auto instruction_with_index_list : instructions_with_index_copy) {
                auto ir_inst = instruction_with_index_list.instruction;
                size_t op_idx = instruction_with_index_list.operand_index;

                auto ir_deference_pointer =
                    ir::DeferencePointer::create(ir_pointer_get_element_ptr);
                auto iter_inst = std::find(RANGE(ir_inst->parent_block->values), ir_inst);
                ir_inst->parent_block->insert(iter_inst, ir_deference_pointer);
                ir_inst->operand(op_idx, ir_deference_pointer);
            }

            ir_index_pointer->finalize();
        }

        return !ir_index_pointers.empty();
    }

    bool convertGetAddressOfVaraibleLikedToPointer(std::shared_ptr<ir::Function> ir_function) {
        auto ir_get_addresses =
            utility::getValuesInFunction<ir::GetAddressOfVariableLiked>(ir_function);

        for (auto ir_get_address : ir_get_addresses) {
            auto instructions_with_index_copy = ir_get_address->instruction_with_index_list;
            for (auto instruction_with_index_list : instructions_with_index_copy) {
                auto ir_inst = instruction_with_index_list.instruction;
                size_t op_idx = instruction_with_index_list.operand_index;

                auto ir_deference_pointer = cast<ir::DeferencePointer>(ir_get_address->variable());
                PRAJNA_ASSERT(ir_deference_pointer,
                              "需要将VariableLiked都转换为DeferencePoitner后再执行该操作");
                ir_deference_pointer->pointer();
                ir_inst->operand(op_idx, ir_deference_pointer->pointer());
            }

            ir_get_address->parent_block->remove(ir_get_address);
            ir_get_address->finalize();
        }

        return !ir_get_addresses.empty();
    }

    bool convertDeferencePointerToStoreAndLoadPointer(std::shared_ptr<ir::Function> ir_function) {
        auto ir_deference_pointers =
            utility::getValuesInFunction<ir::DeferencePointer>(ir_function);

        for (auto ir_deference_pointer : ir_deference_pointers) {
            auto ir_pointer = ir_deference_pointer->pointer();
            auto iter_deference_pointer =
                ir_deference_pointer->parent_block->find(ir_deference_pointer);
            auto instructions_with_index_copy = ir_deference_pointer->instruction_with_index_list;
            for (auto instruction_with_index : instructions_with_index_copy) {
                auto ir_inst = instruction_with_index.instruction;
                size_t op_idx = instruction_with_index.operand_index;

                if (is<ir::WriteVariableLiked>(ir_inst) && op_idx == 1) {
                    auto ir_write_variable_liked = cast<ir::WriteVariableLiked>(ir_inst);
                    auto ir_store =
                        ir::StorePointer::create(ir_write_variable_liked->value(), ir_pointer);
                    utility::replaceInBlock(ir_write_variable_liked, ir_store);
                } else {
                    auto ir_load = ir::LoadPointer::create(ir_pointer);
                    ir_deference_pointer->parent_block->insert(iter_deference_pointer, ir_load);
                    ir_inst->operand(op_idx, ir_load);
                }
            }
            ir_deference_pointer->parent_block->erase(iter_deference_pointer);
            ir_deference_pointer->finalize();
        }

        return !ir_deference_pointers.empty();
    }

    bool runOnFunction(std::shared_ptr<ir::Function> ir_function) override {
        bool changed = false;
        changed = this->insertValueToBlock(ir_function) || changed;
        changed = this->convertThisWrapperToDeferencePointer(ir_function) || changed;
        changed = this->convertVariableToDeferencePointer(ir_function) || changed;
        changed = this->convertAccessFieldToGetStructElementPointer(ir_function) || changed;
        changed = this->convertIndexArrayToGetArrayElementPointer(ir_function) || changed;
        changed = this->convertIndexPointerToGetPointerElementPointer(ir_function) || changed;
        // 需要把VariableLiked都转换完了后再执行
        changed = this->convertGetAddressOfVaraibleLikedToPointer(ir_function) || changed;
        changed = this->convertDeferencePointerToStoreAndLoadPointer(ir_function) || changed;

        return changed;
    }
};

}  // namespace prajna::transform
