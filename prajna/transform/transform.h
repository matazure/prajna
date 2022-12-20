#pragma once

#include <memory>
#include <stack>

#include "prajna/ir/ir.hpp"
#include "prajna/logger.hpp"
#include "prajna/lowering/statement_lowering_visitor.hpp"
#include "prajna/parser/parse.h"
#include "prajna/transform/extract_gpu_grid_pass.hpp"
#include "prajna/transform/initializer_and_copy_destroy_callback.hpp"
#include "prajna/transform/transform_pass.hpp"
#include "prajna/transform/utility.hpp"

namespace prajna::ir {
class Module;
}

namespace prajna::ast {
class Statements;
}

namespace prajna::transform {

std::shared_ptr<ir::Module> flatternBlock(std::shared_ptr<ir::Module> ir_module);

std::shared_ptr<ir::Module> convertVariableToPointer(std::shared_ptr<ir::Module> ir_module);

std::shared_ptr<ir::Module> makeCompatiableWithLlvm(std::shared_ptr<ir::Module> ir_module);

std::shared_ptr<ir::Module> sperateModule(std::shared_ptr<ir::Module> ir_module);

// auto create = [=](auto )
inline std::shared_ptr<ir::Module> convertPropertyToFunctionCall(
    std::shared_ptr<ir::Module> ir_module) {
    for (auto ir_function : ir_module->functions) {
        auto ir_access_properties = utility::getValuesInFunction<ir::AccessProperty>(ir_function);
        for (auto ir_access_property : ir_access_properties) {
            auto ir_block = ir_access_property->parent_block;
            lowering::IrBuilder ir_builder;
            ir_builder.current_block = ir_block;
            ir_builder.inserter_iterator = std::find(RANGE(ir_block->values), ir_access_property);

            auto instructions_with_index_set_copy = ir_access_property->instruction_with_index_list;

            for (auto instruction_with_index : instructions_with_index_set_copy) {
                auto ir_inst = instruction_with_index.instruction;
                size_t op_idx = instruction_with_index.operand_index;

                PRAJNA_ASSERT(not is<ir::GetAddressOfVariableLiked>(ir_inst));

                if (is<ir::WriteProperty>(ir_inst) && op_idx == 1) {
                    auto ir_write_property = cast<ir::WriteProperty>(ir_inst);
                    auto ir_arguments = ir_access_property->arguments();
                    ir_arguments.insert(ir_arguments.begin(), ir_access_property->thisPointer());
                    ir_arguments.push_back(ir_write_property->value());
                    auto ir_setter_call = ir_builder.create<ir::Call>(
                        ir_access_property->property->setter_function, ir_arguments);
                    utility::removeFromParent(ir_write_property);
                    ir_write_property->finalize();
                } else {
                    auto ir_arguments = ir_access_property->arguments();
                    ir_arguments.insert(ir_arguments.begin(), ir_access_property->thisPointer());
                    auto ir_getter_call = ir_builder.create<ir::Call>(
                        ir_access_property->property->getter_function, ir_arguments);
                    ir_inst->operand(ir_getter_call, op_idx);
                }
            }

            if (instructions_with_index_set_copy.empty()) {
                auto ir_arguments = ir_access_property->arguments();
                ir_arguments.insert(ir_arguments.begin(), ir_access_property->thisPointer());
                auto ir_getter_call = ir_builder.create<ir::Call>(
                    ir_access_property->property->getter_function, ir_arguments);
            }

            utility::removeFromParent(ir_access_property);
            ir_access_property->finalize();
        }
    }
    return ir_module;
}

inline std::shared_ptr<ir::Module> convertKernelFunctionCallToKernelLaunch(
    std::shared_ptr<ir::Module> ir_module) {
    for (auto ir_function : ir_module->functions) {
        auto ir_kernel_function_calls =
            utility::getValuesInFunction<ir::KernelFunctionCall>(ir_function);
        for (auto ir_kernel_function_call : ir_kernel_function_calls) {
            auto ir_kernel_function = ir_kernel_function_call->function();
            auto ir_grid_dim = ir_kernel_function_call->gridDim();
            auto ir_block_dim = ir_kernel_function_call->blockDim();
            // auto ir_arguments = ir_kernel_function_call->arguments();
            auto ir_block = ir_kernel_function_call->parent_block;

            lowering::IrBuilder ir_builder;
            ir_builder.current_block = ir_block;
            ir_builder.inserter_iterator =
                std::find(RANGE(ir_block->values), ir_kernel_function_call);

            // 构建::cuda::launchKernel的逻辑
            auto ir_kernel_arguments_address_array_i8ptr = ir_builder.create<ir::LocalVariable>(
                ir::ArrayType::create(ir::PointerType::create(ir::IntType::create(8, true)),
                                      ir_kernel_function_call->argumentSize()));
            for (size_t i = 0; i < ir_kernel_function_call->argumentSize(); ++i) {
                auto ir_argument = ir_kernel_function_call->argument(i);
                auto ir_kernel_argument_address_i8ptr = ir_builder.create<ir::BitCast>(
                    ir_builder.create<ir::GetAddressOfVariableLiked>(
                        ir_builder.variableLikedNormalize(ir_argument)),
                    ir::PointerType::create(ir::IntType::create(8, true)));
                auto ir_array_index = ir_builder.create<ir::IndexArray>(
                    ir_kernel_arguments_address_array_i8ptr, ir_builder.getIndexConstant(i));
                auto ir_array_index_write = ir_builder.create<ir::WriteVariableLiked>(
                    ir_kernel_argument_address_i8ptr, ir_array_index);
            }

            auto ir_launch_function = lowering::symbolGet<ir::Value>(
                lowering::symbolGet<lowering::SymbolTable>(
                    ir_module->symbol_table->rootSymbolTable()->get("gpu"))
                    ->get("launchKernel"));
            PRAJNA_ASSERT(ir_launch_function);
            std::vector<std::shared_ptr<ir::Value>> ir_arguments(4);
            ir_arguments[0] = ir_builder.create<ir::BitCast>(
                ir_kernel_function, ir::PointerType::create(ir::IntType::create(8, true)));
            ir_arguments[1] = ir_grid_dim;
            ir_arguments[2] = ir_block_dim;
            auto ir_array_index0 = ir_builder.create<ir::IndexArray>(
                ir_kernel_arguments_address_array_i8ptr, ir_builder.getIndexConstant(0));
            auto ir_array_address = ir_builder.create<ir::BitCast>(
                ir_builder.create<ir::GetAddressOfVariableLiked>(ir_array_index0),
                ir::PointerType::create(ir::PointerType::create(ir::IntType::create(8, true))));
            ir_arguments[3] = ir_array_address;
            ir_builder.create<ir::Call>(ir_launch_function, ir_arguments);

            utility::removeFromParent(ir_kernel_function_call);
            ir_kernel_function_call->finalize();
        }
    }

    return ir_module;
}

inline std::shared_ptr<ir::Module> convertKernelFunctionOperandToAddress(
    std::shared_ptr<ir::Module> ir_module) {
    for (auto ir_function : ir_module->functions) {
        auto ir_instructions = utility::getValuesInFunction<ir::Instruction>(ir_function);

        for (auto ir_instruction : ir_instructions) {
            for (size_t i = 0; i < ir_instruction->operandSize(); ++i) {
                if (auto ir_function = cast<ir::Function>(ir_instruction->operand(i))) {
                    if (ir_function->function_type->annotations.count("kernel")) {
                        auto global_variable_fullname =
                            getKernelFunctionAddressName(ir_function->function_type->fullname);

                        sp<ir::GlobalVariable> ir_global_variable = nullptr;
                        auto iter_global_variable = std::find_if(
                            RANGE(ir_module->global_variables), [=](sp<ir::GlobalVariable> x) {
                                return x->fullname == global_variable_fullname;
                            });
                        if (iter_global_variable != ir_module->global_variables.end()) {
                            ir_global_variable = *iter_global_variable;
                        } else {
                            ir_global_variable = ir::GlobalVariable::create(ir_function->type);
                            ir_global_variable->name = global_variable_fullname;
                            ir_global_variable->fullname = ir_global_variable->name;
                            ir_global_variable->parent_module = ir_module;
                            // 如果不是同一个module的, 则为external, 目前所有的nvptx
                            // IR都会迁移的使用的Module里去
                            // ir_global_variable->is_external =
                            //     ir_function->parent_module != ir_module;
                            ir_module->global_variables.push_back(ir_global_variable);
                        }

                        ir_instruction->operand(ir_global_variable, i);
                    }
                }
            }
        }
    }
    return ir_module;
}

inline sp<ir::Module> convertGlobalVariableToPointer(sp<ir::Module> ir_module) {
    for (auto ir_global_variable : ir_module->global_variables) {
        auto ir_global_alloca = ir::GlobalAlloca::create(ir_global_variable->type);
        ir_global_alloca->name = ir_global_variable->name;
        ir_global_alloca->fullname = ir_global_variable->fullname;
        ir_global_alloca->parent_module = ir_module;
        // ir_global_variable->is_external默认为false
        ir_global_alloca->is_external = ir_global_variable->is_external;
        ir_module->global_allocas.push_back(ir_global_alloca);
    }

    ir_module->global_variables.clear();

    for (auto ir_function : ir_module->functions) {
        auto ir_instructions = utility::getValuesInFunction<ir::Instruction>(ir_function);
        for (auto ir_instruction : ir_instructions) {
            for (size_t i = 0; i < ir_instruction->operandSize(); ++i) {
                // @note 全局变量目前遵循如果使用其他module的则自身为external的原则
                if (auto ir_global_variable =
                        cast<ir::GlobalVariable>(ir_instruction->operand(i))) {
                    auto iter_global_alloca =
                        std::find_if(RANGE(ir_module->global_allocas), [=](sp<ir::GlobalAlloca> x) {
                            return x->fullname == ir_global_variable->fullname;
                        });
                    sp<ir::GlobalAlloca> ir_global_alloca = nullptr;
                    if (iter_global_alloca != ir_module->global_allocas.end()) {
                        ir_global_alloca = *iter_global_alloca;
                    } else {
                        ir_global_alloca = ir::GlobalAlloca::create(ir_global_variable->type);
                        ir_global_alloca->name = ir_global_variable->name;
                        ir_global_alloca->fullname = ir_global_variable->fullname;
                        ir_global_alloca->parent_module = ir_module;
                        ir_global_alloca->is_external = true;
                        ir_module->global_allocas.push_back(ir_global_alloca);
                    }

                    auto ir_deference_pointer = ir::DeferencePointer::create(ir_global_alloca);
                    auto ir_block = ir_instruction->parent_block;
                    auto iter =
                        std::find(ir_block->values.begin(), ir_block->values.end(), ir_instruction);
                    ir_block->insert(iter, ir_deference_pointer);
                    ir_instruction->operand(ir_deference_pointer, i);
                }
            }
        }
    }

    return ir_module;
}

inline std::shared_ptr<ir::Module> cloneExternalNvptxValue(std::shared_ptr<ir::Module> ir_module) {
    if (ir_module->modules.count(ir::Target::nvptx) == 0) {
        return ir_module;
    }

    auto ir_nvptx_module = ir_module->modules[ir::Target::nvptx];
    std::list<std::shared_ptr<ir::Function>> ir_function_seeds(ir_nvptx_module->functions.rbegin(),
                                                               ir_nvptx_module->functions.rend());
    std::list<std::shared_ptr<ir::Function>> ir_external_functions;
    for (auto iter_function = ir_function_seeds.begin(); iter_function != ir_function_seeds.end();
         ++iter_function) {
        auto ir_function = *iter_function;
        auto ir_instructions = utility::getValuesInFunction<ir::Instruction>(ir_function);
        for (auto ir_instruction : ir_instructions) {
            for (size_t i = 0; i < ir_instruction->operandSize(); ++i) {
                if (auto ir_function_type = ir_instruction->operand(i)->getFunctionType()) {
                    auto ir_function_used = ir_function_type->function;
                    if (std::count(RANGE(ir_function_seeds), ir_function_used) == 0) {
                        ir_function_seeds.push_back(ir_function_used);
                        ir_external_functions.push_back(ir_function_used);
                    }
                }
            }
        }
    }

    ir_external_functions.reverse();
    auto ir_cloner = std::make_shared<ir::Cloner>();
    std::transform(RANGE(ir_external_functions), ir_external_functions.begin(),
                   [=](std::shared_ptr<ir::Function> ir_function) {
                       auto ir_new_function = cast<ir::Function>(ir_function->clone(ir_cloner));
                       ir_new_function->parent_module = ir_nvptx_module;
                       return ir_new_function;
                   });

    auto ir_all_functions = ir_external_functions;
    ir_all_functions.merge(ir_nvptx_module->functions);
    ir_nvptx_module->functions = ir_all_functions;

    std::cout << "functions---------------------\n";
    for (auto ir_function : ir_nvptx_module->functions) {
        std::cout << ir_function->fullname << "\n";
    }

    return ir_module;
}

inline std::shared_ptr<ir::Module> defineKernelFunctionAddress(
    std::shared_ptr<ir::Module> ir_module) {
    if (ir_module->modules.count(ir::Target::nvptx) == 0) {
        return ir_module;
    }

    auto ir_nvptx_module = ir_module->modules[ir::Target::nvptx];
    for (auto ir_function : ir_nvptx_module->functions) {
        if (ir_function->function_type->annotations.count("kernel")) {
            auto global_variable_fullname =
                getKernelFunctionAddressName(ir_function->function_type->fullname);
            auto iter_global_variable = std::find_if(
                RANGE(ir_module->global_variables),
                [=](sp<ir::GlobalVariable> x) { return x->fullname == global_variable_fullname; });
            if (iter_global_variable == ir_module->global_variables.end()) {
                auto ir_global_variable = ir::GlobalVariable::create(ir_function->type);
                ir_global_variable->name = global_variable_fullname;
                ir_global_variable->fullname = ir_global_variable->name;
                ir_global_variable->parent_module = ir_module;
                ir_module->global_variables.push_back(ir_global_variable);
            }
        }
    }

    return ir_module;
}

// @brief 移除return后面的指令. 若不移除, 会存在未知错误
inline std::shared_ptr<ir::Module> removeValuesAfterReturn(std::shared_ptr<ir::Module> ir_module) {
    for (auto ir_function : ir_module->functions) {
        for (auto ir_block : ir_function->blocks) {
            auto iter_return =
                std::find_if(RANGE(ir_block->values), [](auto x) { return is<ir::Return>(x); });
            if (iter_return != ir_block->values.end()) {
                ir_block->values.erase(std::next(iter_return), ir_block->values.end());
            }
        }
    }

    return ir_module;
}

inline std::shared_ptr<ir::Module> transform(std::shared_ptr<ir::Module> ir_module) {
    ir_module = convertPropertyToFunctionCall(ir_module);
    ir_module = insertInitializeAndCopyAndDestroyCallback(ir_module);
    ir_module = flatternBlock(ir_module);
    ir_module = removeValuesAfterReturn(ir_module);
    ir_module = extractGpuFor(ir_module);
    ir_module = convertKernelFunctionCallToKernelLaunch(ir_module);
    ir_module = convertKernelFunctionOperandToAddress(ir_module);
    ir_module = convertGlobalVariableToPointer(ir_module);
    ir_module = convertVariableToPointer(ir_module);
    ir_module = sperateModule(ir_module);
    ir_module = cloneExternalNvptxValue(ir_module);
    ir_module = defineKernelFunctionAddress(ir_module);
    ir_module = convertGlobalVariableToPointer(ir_module);

    // 在sperateModule后面
    ir_module = makeCompatiableWithLlvm(ir_module);
    return ir_module;
}
}  // namespace prajna::transform
