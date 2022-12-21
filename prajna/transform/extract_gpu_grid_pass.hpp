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

// class ExtractGpuForPass : public FunctionPass {
//    public:
//     std::shared_ptr<ir::Function> createKernelFunction(
//         std::shared_ptr<ir::For> ir_gpu_for,
//         std::vector<std::shared_ptr<ir::LocalVariable>> ir_variables,
//         std::string ir_kernel_function_name) {
//         std::vector<std::shared_ptr<ir::Type>> ir_argument_types(ir_variables.size());
//         std::transform(RANGE(ir_variables), ir_argument_types.begin(),
//                        [](std::shared_ptr<ir::Value> ir_value) { return ir_value->type; });

//         auto ir_host_function = ir_gpu_for->getParentFunction();
//         auto ir_host_module = ir_host_function->parent_module;

//         auto ir_kernel_function_type =
//             ir::FunctionType::create(ir::VoidType::create(), ir_argument_types);
//         auto ir_kernel_function = ir::Function::create(ir_kernel_function_type);

//         auto ir_nvptx_module = ir_host_module->modules[ir::Target::nvptx];

//         ir_nvptx_module->functions.push_back(ir_kernel_function);
//         //
//         ir_kernel_function->name = ir_kernel_function_name;
//         ir_kernel_function->fullname =
//             concatFullname(ir_host_function->fullname, ir_kernel_function->name);
//         ir_kernel_function->parent_module = ir_nvptx_module;
//         ir_kernel_function->function_type->annotations["target"].push_back("nvptx");
//         ir_kernel_function->function_type->annotations.insert({"kernel", {}});

//         auto ir_grid_block = ir_gpu_for->loopBlock();
//         ir_grid_block->parent_block = nullptr;
//         ir_kernel_function->arguments.resize(ir_kernel_function_type->argument_types.size());
//         for (size_t i = 0; i < ir_kernel_function_type->argument_types.size(); ++i) {
//             ir_kernel_function->arguments[i] = ir::Argument::create(ir_argument_types[i]);
//             ir_kernel_function->arguments[i]->parent_block = ir_grid_block;
//         }

//         //
//         auto ir_top_block = ir::Block::create();
//         ir_top_block->parent_function = ir_kernel_function;
//         ir_kernel_function->blocks.push_back(ir_top_block);
//         auto iter = ir_top_block->values.end();

//         {
//             std::string code = "var threadIdx_x = threadIdxX();";
//             auto logger = Logger::create(code);
//             auto symbol_table = ir_gpu_for->getParentFunction()->parent_module->symbol_table;
//             auto statement_lowering_visitor =
//                 lowering::StatementLoweringVisitor::create(symbol_table, logger);
//             auto ir_builder = statement_lowering_visitor->ir_builder;
//             ir_builder->pushSymbolTable();
//             ir_builder->pushBlock(ir_top_block);
//             // ir_builder->symbol_table->set(ir_tid_x_fun, "getThreadIdxX");

//             auto ast = prajna::parser::parse(code, "//None", logger);

//             statement_lowering_visitor->apply(ast);

//             ir_builder->create<ir::Return>(ir::VoidValue::create());
//             ir_builder->popSymbolTable();
//             ir_builder->popBlock(ir_top_block);
//         }

//         return ir_kernel_function;

//         // // 将捕获的变量替换为核函数的参数
//         // for (auto [ir_variable, ir_argument] :
//         //      boost::combine(ir_variables, ir_kernel_function->arguments)) { //
//         //      combine会使用最短的size
//         //     auto instruction_with_index_list =
//         //     ir_variable->instruction_with_index_list; for (auto
//         //     [ir_instruction, idx] : instruction_with_index_list) {
//         //         //  只处理相关的操作, ir_grid外的不处理
//         //         if (ir_instruction->parent_block == ir_grid_block) {
//         //             ir_instruction->operand(idx, ir_argument);
//         //         }
//         //     }
//         // }
//     }

//     void conveterForToGpu(std::shared_ptr<ir::For> ir_gpu_for, size_t idx) {
//         auto ir_captured_variable_vector =
//             utility::captureExternalVariablesInBlock(ir_gpu_for->loopBlock());
//         // 将index移除, 其会转换为核函数的内部参数
//         ir_captured_variable_vector.remove(ir_gpu_for->index());
//         utility::removeFromParent(ir_gpu_for->index());
//         // 都是可捕获类型
//         if (std::any_of(RANGE(ir_captured_variable_vector), [](auto ir_variable) {
//                 return !utility::isCapturedType(ir_variable->type);
//             })) {
//             PRAJNA_TODO;
//         }
//         utility::eachValue(ir_gpu_for->loopBlock(), [=](auto ir_value) {
//             // 不能被修改
//             if (auto ir_write_variable_liked = cast<ir::WriteVariableLiked>(ir_value)) {
//                 if (std::any_of(RANGE(ir_captured_variable_vector), [=](auto
//                 ir_captured_variable) {
//                         return utility::isReferedTo(ir_captured_variable,
//                                                     ir_write_variable_liked->variable());
//                     })) {
//                     PRAJNA_TODO;
//                 }
//             }
//             // 不能获取地址, 因为是通过值拷贝捕获的
//             if (auto ir_get_address_of = cast<ir::GetAddressOfVariableLiked>(ir_value)) {
//                 if (std::any_of(RANGE(ir_captured_variable_vector), [=](auto
//                 ir_captured_variable) {
//                         return ir_captured_variable == ir_get_address_of->variable();
//                     })) {
//                     PRAJNA_TODO;
//                 }
//             }
//         });

//         // 参数需要有顺序
//         std::vector<std::shared_ptr<ir::LocalVariable>> ir_captured_variable_vec;
//         auto ir_kernel_function = this->createKernelFunction(ir_gpu_for,
//         ir_captured_variable_vec,
//                                                              "grid_kernel_" +
//                                                              std::to_string(idx));
//         // 核函数并不会在这里生成, 起会在JIT的时候生成PTX,
//         // 所以我们在这里用全局变量来表示它, 回头生产了再赋予全局变量,
//         // 如果这里立即生成, 则代码的模块性会大受影响=\-
//         auto ir_global_variable =
//             ir::GlobalVariable::create(ir::PointerType::create(ir::IntType::create(64, 32)));
//         ir_global_variable->parent_module = ir_gpu_for->getParentFunction()->parent_module;
//         ir_global_variable->fullname = ir_kernel_function->fullname + "_pointer";
//         // 调用核函数
//         // lauchKernelFunction(ir_global_variable, gridX, )
//         // cuda::cu

//         utility::removeFromParent(ir_gpu_for);
//     }

//     bool runOnFunction(std::shared_ptr<ir::Function> ir_kernel_function) override {
//         bool changed = true;

//         auto ir_grids = utility::getValuesInFunction<ir::For>(ir_kernel_function);

//         size_t i = 0;
//         for (auto ir_gpu_for : ir_grids) {
//             this->conveterForToGpu(ir_gpu_for, i++);
//         }

//         return changed;
//     }
// };

inline auto convertGpuForToKernelCall(std::shared_ptr<ir::For> ir_gpu_for, size_t idx) {
    auto ir_module = ir_gpu_for->getParentFunction()->parent_module;
    auto ir_nvptx_module = ir_module->modules[ir::Target::nvptx];

    auto ir_captured_variables_list =
        utility::captureExternalVariablesInBlock(ir_gpu_for->loopBlock());
    // 将index, first, last
    ir_captured_variables_list.remove(ir_gpu_for->index());
    // todo
    utility::removeFromParent(ir_gpu_for->index());

    std::vector<std::shared_ptr<ir::Type>> ir_argument_types(2);
    // 加入first和last
    ir_argument_types[0] = ir_gpu_for->first()->type;
    ir_argument_types[1] = ir_gpu_for->last()->type;
    std::transform(RANGE(ir_captured_variables_list), std::back_inserter(ir_argument_types),
                   [](std::shared_ptr<ir::Value> ir_value) {
                       if (utility::isHostTensorType(ir_value->type)) {
                           return utility::getGpuTensorTypeOfHostTensorType(ir_value->type);
                       } else {
                           return ir_value->type;
                       }
                   });

    auto ir_kernel_function_type =
        ir::FunctionType::create(ir::VoidType::create(), ir_argument_types);
    auto ir_kernel_function = ir::Function::create(ir_kernel_function_type);
    ir_kernel_function->fullname =
        concatFullname(ir_gpu_for->getParentFunction()->fullname, "gpu_for_" + std::to_string(idx));
    ir_kernel_function->name = ir_kernel_function->fullname;
    ir_kernel_function_type->fullname = ir_kernel_function->fullname;
    ir_kernel_function_type->name = ir_kernel_function->fullname;
    ir_kernel_function->parent_module = ir_nvptx_module;
    ir_kernel_function->function_type->annotations["target"].push_back("nvptx");
    ir_kernel_function->function_type->annotations.insert({"kernel", {}});
    ir_nvptx_module->functions.push_back(ir_kernel_function);

    auto ir_block = ir::Block::create();
    ir_block->parent_function = ir_kernel_function;
    ir_kernel_function->blocks.push_back(ir_block);

    auto ir_builder = std::make_shared<lowering::IrBuilder>();
    ir_builder->current_block = ir_block;
    ir_builder->inserter_iterator = ir_block->values.end();

    std::unordered_map<std::shared_ptr<ir::Value>, std::shared_ptr<ir::Value>> variables_dict;
    auto iter_captured_variable = ir_captured_variables_list.begin();
    ir_kernel_function->arguments.resize(ir_argument_types.size());
    auto ir_first = ir_builder->create<ir::Argument>(ir_argument_types[0]);
    variables_dict[ir_gpu_for->first()] = ir_first;
    ir_kernel_function->arguments[0] = ir_first;
    auto ir_last = ir_builder->create<ir::Argument>(ir_argument_types[1]);
    variables_dict[ir_gpu_for->last()] = ir_last;
    ir_kernel_function->arguments[1] = ir_last;
    for (size_t i = 2; i < ir_argument_types.size(); ++i, ++iter_captured_variable) {
        auto ir_argument = ir_builder->create<ir::Argument>(ir_argument_types[i]);
        ir_kernel_function->arguments[i] = ir_argument;
        // 需要搞成临时变量, 这样才会原来的变量对应, 以便访问成员函数等
        variables_dict[*iter_captured_variable] = ir_builder->variableLikedNormalize(ir_argument);
    }

    // 将捕获的变量置换为参数对应的临时变量
    for (auto ir_captured_variable : ir_captured_variables_list) {
        auto instruction_with_index_inner_list = ir_captured_variable->instruction_with_index_list;
        instruction_with_index_inner_list.remove_if(
            [=](ir::InstructionWithOperandIndex instruction_with_operand_index) -> bool {
                return instruction_with_operand_index.instruction->getRootBlock() !=
                       ir_gpu_for->loopBlock();
            });
        for (auto instruction_with_operand_index : instruction_with_index_inner_list) {
            auto ir_instruction = instruction_with_operand_index.instruction;
            auto operand_index = instruction_with_operand_index.operand_index;
            PRAJNA_ASSERT(variables_dict.count(ir_captured_variable));
            ir_instruction->operand(operand_index, variables_dict[ir_captured_variable]);
        }
    }

    auto ir_index = ir_builder->create<ir::LocalVariable>(ir_builder->getIndexType());
    ir_index->name = "i";
    auto ir_gpu_for_index_inst_with_idx_list_copy =
        ir_gpu_for->index()->instruction_with_index_list;
    for (auto inst_with_idx : ir_gpu_for_index_inst_with_idx_list_copy) {
        auto ir_instruction = inst_with_idx.instruction;
        // ir_gpu_for将被移除, 不能再使用ir_index
        if (ir_instruction == ir_gpu_for) continue;

        auto operand_index = inst_with_idx.operand_index;
        ir_instruction->operand(operand_index, ir_index);
    }

    {
        std::string code =
            "var thread_idx = gpu::threadIndex();"
            "var block_idx = gpu::blockIndex();"
            "var block_dim = gpu::blockDim();"
            "var grid_dim = gpu::gridDim();"
            "i = first + thread_idx[0] + block_idx[0] * block_dim[0];"
            "while (i < last){"
            "   i = i + block_dim[0] * grid_dim[0];"
            "}";

        auto logger = Logger::create(code);
        auto symbol_table = ir_module->symbol_table;
        auto statement_lowering_visitor =
            lowering::StatementLoweringVisitor::create(symbol_table, logger);
        auto ir_builder = statement_lowering_visitor->ir_builder;
        ir_builder->pushSymbolTable();
        ir_builder->pushBlock(ir_block);

        ir_builder->symbol_table->set(ir_index, "i");
        ir_builder->symbol_table->set(ir_first, "first");
        ir_builder->symbol_table->set(ir_last, "last");

        auto ast = prajna::parser::parse(code, "//None", logger);

        statement_lowering_visitor->apply(ast);
        ir_builder->popSymbolTable();
        ir_builder->popBlock(ir_block);

        // 插入ir_gpu_for里的逻辑
        auto ir_kernel_while = cast<ir::While>(*std::prev(ir_block->values.end(), 2));
        PRAJNA_ASSERT(ir_kernel_while);
        auto ir_kernel_while_loop_block =
            cast<ir::Block>(ir_kernel_while->loopBlock()->values.front());
        PRAJNA_ASSERT(ir_kernel_while_loop_block);
        auto ir_while_builder = std::make_shared<lowering::IrBuilder>();
        ir_while_builder->current_block = ir_kernel_while_loop_block;
        ir_while_builder->inserter_iterator = ir_kernel_while_loop_block->values.begin();
        for (auto ir_value : ir_gpu_for->loopBlock()->values) {
            ir_while_builder->insert(ir_value);
        }
    }

    ir_builder->create<ir::Return>(ir_builder->create<ir::VoidValue>());

    // @note 临时处理, 应该搞到外面才合理
    // FlatternBlockPass flattern_block_pass;
    // flattern_block_pass.runOnFunction(ir_kernel_function);

    return std::make_tuple(ir_kernel_function, ir_captured_variables_list);
}

inline std::shared_ptr<ir::Module> extractGpuFor(std::shared_ptr<ir::Module> ir_module) {
    auto ir_gpu_fors = utility::getValuesInModule<ir::For>(ir_module);
    ir_gpu_fors.remove_if([](std::shared_ptr<ir::For> ir_gpu_for) {
        return not ir_gpu_for->annotations.count("gpu");
    });

    size_t idx = 0;
    for (auto ir_gpu_for : ir_gpu_fors) {
        auto [ir_kernel_function, ir_captured_variables_list] =
            convertGpuForToKernelCall(ir_gpu_for, idx);

        auto ir_gpu_parent_block = ir_gpu_for->parent_block;
        auto iter_gpu_for = std::find(RANGE(ir_gpu_parent_block->values), ir_gpu_for);
        auto ir_builder = std::make_shared<lowering::IrBuilder>();
        ir_builder->current_block = ir_gpu_parent_block;
        ir_builder->inserter_iterator = iter_gpu_for;
        ir_builder->symbol_table = ir_module->symbol_table;

        //
        auto symbol_table_gpu =
            lowering::symbolGet<lowering::SymbolTable>(ir_module->symbol_table->get("gpu"));
        PRAJNA_ASSERT(symbol_table_gpu);
        auto ir_max_thread_per_block_function =
            lowering::symbolGet<ir::Value>(symbol_table_gpu->get("maxThreadPerBlock"));
        PRAJNA_ASSERT(ir_max_thread_per_block_function);
        auto ir_multi_processor_count_function =
            lowering::symbolGet<ir::Value>(symbol_table_gpu->get("multiProcessorsCount"));
        PRAJNA_ASSERT(ir_multi_processor_count_function);

        auto ir_zero = ir_builder->getIndexConstant(0);
        auto ir_max_thread_per_block = ir_builder->create<ir::Call>(
            ir_max_thread_per_block_function, std::vector<std::shared_ptr<ir::Value>>{ir_zero});
        auto ir_multi_process_count = ir_builder->create<ir::Call>(
            ir_multi_processor_count_function, std::vector<std::shared_ptr<ir::Value>>{ir_zero});

        auto ir_grid_dim = ir_builder->create<ir::LocalVariable>(ir_builder->getDim3Type());
        ir_builder->setDim3(ir_grid_dim, 0, ir_multi_process_count);
        ir_builder->setDim3(ir_grid_dim, 1, ir_builder->getIndexConstant(1));
        ir_builder->setDim3(ir_grid_dim, 2, ir_builder->getIndexConstant(1));

        auto ir_block_dim = ir_builder->create<ir::LocalVariable>(ir_builder->getDim3Type());
        ir_builder->setDim3(ir_block_dim, 0, ir_max_thread_per_block);
        ir_builder->setDim3(ir_block_dim, 1, ir_builder->getIndexConstant(1));
        ir_builder->setDim3(ir_block_dim, 2, ir_builder->getIndexConstant(1));

        std::vector<std::shared_ptr<ir::Value>> ir_arguments;
        ir_arguments.push_back(ir_gpu_for->first());
        ir_arguments.push_back(ir_gpu_for->last());
        std::unordered_map<std::shared_ptr<ir::Value>, std::shared_ptr<ir::Variable>>
            gpu_host_tensor_dict;
        std::transform(
            RANGE(ir_captured_variables_list), std::back_inserter(ir_arguments),
            [=, &gpu_host_tensor_dict](
                std::shared_ptr<ir::Variable> ir_captured_variable) -> std::shared_ptr<ir::Value> {
                if (utility::isHostTensorType(ir_captured_variable->type)) {
                    auto ir_gpu_tensor =
                        ir_builder->callMemberFunction(ir_captured_variable, "toGpu", {});
                    gpu_host_tensor_dict[ir_gpu_tensor] = ir_captured_variable;
                    return ir_gpu_tensor;
                } else {
                    return ir_captured_variable;
                }
            });

        ir_builder->create<ir::KernelFunctionCall>(ir_kernel_function, ir_grid_dim, ir_block_dim,
                                                   ir_arguments);
        for (auto [ir_gpu_tensor, ir_host_tensor_variable] : gpu_host_tensor_dict) {
            PRAJNA_ASSERT(utility::isGpuTensorType(ir_gpu_tensor->type));
            auto ir_host_tensor = ir_builder->callMemberFunction(ir_gpu_tensor, "toHost", {});
            ir_builder->create<ir::WriteVariableLiked>(ir_host_tensor, ir_host_tensor_variable);
        }

        utility::removeFromParent(ir_gpu_for);
        ir_gpu_for->finalize();
        ++idx;
    }

    return ir_module;
}

}  // namespace prajna::transform
