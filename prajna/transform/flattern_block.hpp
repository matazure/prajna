#pragma once

#include <boost/range/combine.hpp>

#include "prajna/ir/ir.hpp"
#include "prajna/logger.hpp"
#include "prajna/lowering/statement_lowering_visitor.hpp"
#include "prajna/parser/parse.h"
#include "prajna/transform/transform_pass.hpp"
#include "prajna/transform/transform_to_ssa_pass.hpp"
#include "prajna/transform/utility.hpp"

namespace prajna::transform {

namespace {

inline bool flatternBlockImpl(std::shared_ptr<ir::Block> ir_block) {
    bool changed = false;
    for (auto iter = ir_block->values.begin(); iter != ir_block->values.end();) {
        if (auto ir_cur_block = cast<ir::Block>(*iter)) {
            // Label也是Block的一种, 但其不能展开
            if (is<ir::Label>(ir_cur_block)) {
                ++iter;
                continue;
            }

            flatternBlockImpl(ir_cur_block);
            for (auto ir_value : ir_cur_block->values) {
                ir_block->insert(iter, ir_value);
            }
            iter = ir_block->values.erase(iter);
            ir_cur_block->finalize();
            changed = true;
            continue;
        }
        if (auto ir_if = cast<ir::If>(*iter)) {
            flatternBlockImpl(ir_if->trueBlock());
            flatternBlockImpl(ir_if->falseBlock());

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
            flatternBlockImpl(ir_while->loopBlock());

            auto ir_label_loop = ir::Label::create();
            ir_while->loopBlock()->pushFront(ir_label_loop);
            // auto ir_label_after_loop = ir::Label::create();
            auto ir_condition_branch = ir::ConditionBranch::create(
                ir_while->condition(), ir_label_loop, ir_while->afterLabel());
            ir_while->conditionBlock()->pushBack(ir_condition_branch);

            auto ir_label_condition_entry = ir_while->beforeLabel();
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
            // ir_block->insert(iter, ir_label_after_loop);

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
            flatternBlockImpl(ir_for->loopBlock());

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

            auto ir_label_condition_entry = ir_for->beforeLabel();
            auto ir_concat_jump = ir_builder->create<ir::JumpBranch>(ir_label_condition_entry);
            ir_block->insert(iter, ir_label_condition_entry);
            auto ir_label_loop = ir::Label::create();
            ir_for->loopBlock()->pushFront(ir_label_loop);
            // insertCallMemmberFunction会插入ir_condition
            auto ir_condition =
                ir_builder->callBinaryOeprator(ir_for->index(), "<", {ir_for->last()});
            auto ir_label_after_loop = ir_for->afterLabel();
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

inline std::list<std::shared_ptr<ir::Block>> splitBlock(std::shared_ptr<ir::Block> ir_top_block) {
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

}  // namespace

inline std::shared_ptr<ir::Module> flatternBlock(std::shared_ptr<ir::Module> ir_module) {
    FlatternBlockPass flattern_block_pass;
    for (auto ir_function : ir_module->functions) {
        // @note 后面可能需要重构, 目前假设只有一个block时才需要展开
        if (ir_function->blocks.size() != 1) continue;

        auto ir_top_block = ir_function->blocks.front();
        flatternBlockImpl(ir_top_block);
        // 分离成标准ssa的block形式
        ir_function->blocks = splitBlock(ir_top_block);
        for (auto ir_block : ir_function->blocks) {
            ir_block->parent_function = ir_function;
            ir_block->parent_block = nullptr;
        }
    }

    for (auto [ir_target, ir_sub_module] : ir_module->modules) {
        if (not ir_sub_module) continue;

        flatternBlock(ir_sub_module);
    }

    return ir_module;
}

}  // namespace prajna::transform
