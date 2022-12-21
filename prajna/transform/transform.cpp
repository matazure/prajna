#include "prajna/transform/transform.h"

#include "prajna/transform/extract_gpu_grid_pass.hpp"
#include "prajna/transform/transform_to_ssa_pass.hpp"

namespace prajna::transform {

std::shared_ptr<ir::Module> convertVariableToPointer(std::shared_ptr<ir::Module> ir_module) {
    PRAJNA_ASSERT(ir_module);

    ConvertVariableToPointerPass var_to_pointer_pass;
    for (auto ir_function : ir_module->functions) {
        var_to_pointer_pass.runOnFunction(ir_function);
    }

    for (auto [ir_target, ir_sub_module] : ir_module->modules) {
        if (not ir_sub_module) continue;

        convertVariableToPointer(ir_sub_module);
    }

    return ir_module;
}

std::shared_ptr<ir::Module> sperateModule(std::shared_ptr<ir::Module> ir_module) {
    for (auto iter_function = ir_module->functions.begin();
         iter_function != ir_module->functions.end();) {
        auto ir_function = *iter_function;
        if (std::count(RANGE(ir_function->function_type->annotations["target"]), "nvptx")) {
            auto ir_nvptx_module = ir_module->modules[ir::Target::nvptx];
            ir_function->parent_module = ir_nvptx_module;
            ir_nvptx_module->functions.push_back(ir_function);
            iter_function = ir_module->functions.erase(iter_function);
        } else {
            ++iter_function;
        }
    }
    return ir_module;
}

}  // namespace prajna::transform
