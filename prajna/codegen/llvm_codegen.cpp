#include "prajna/codegen/llvm_codegen.h"

#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/ConstantFolder.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/ValueHandle.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/Debug.h"
#include "prajna/helper.hpp"
#include "prajna/ir/ir.hpp"
namespace prajna::codegen {

static llvm::LLVMContext static_llvm_context;

class LlvmCodegen {
    LlvmCodegen() {}

   public:
    static std::shared_ptr<LlvmCodegen> create() {
        std::shared_ptr<LlvmCodegen> self(new LlvmCodegen);
        return self;
    }

    void emitType(std::shared_ptr<ir::Type> ir_type) {
        if (ir_type->llvm_type) return;

        // 对于不完备的类型, codegen时选择跳过
        if (auto ir_real_number_type = cast<ir::RealNumberType>(ir_type)) {
            if (ir_real_number_type->bits <= 0) {
                return;
            }
        }

        if (auto ir_bool_type = cast<ir::BoolType>(ir_type)) {
            // TODO 要求使用1位整型来表示bool类型
            ir_bool_type->llvm_type = llvm::Type::getInt1Ty(static_llvm_context);
            return;
        }
        if (auto ir_char_type = cast<ir::CharType>(ir_type)) {
            ir_char_type->llvm_type = llvm::Type::getInt8Ty(static_llvm_context);
            return;
        }
        if (auto ir_int_type = cast<ir::IntType>(ir_type)) {
            ir_int_type->llvm_type = llvm::Type::getIntNTy(static_llvm_context, ir_int_type->bits);
            return;
        }
        if (auto ir_float_type = cast<ir::FloatType>(ir_type)) {
            switch (ir_float_type->bits) {
                case 32:
                    ir_float_type->llvm_type = llvm::Type::getFloatTy(static_llvm_context);
                    return;
                case 64:
                    ir_float_type->llvm_type = llvm::Type::getDoubleTy(static_llvm_context);
                    return;
                default:
                    PRAJNA_TODO;
            }

            return;
        }
        if (auto ir_void_type = cast<ir::VoidType>(ir_type)) {
            ir_void_type->llvm_type = llvm::Type::getVoidTy(static_llvm_context);
            return;
        }
        if (auto ir_function_type = cast<ir::FunctionType>(ir_type)) {
            std::vector<llvm::Type*> llvm_argument_types(ir_function_type->argument_types.size());
            std::transform(ir_function_type->argument_types.begin(),
                           ir_function_type->argument_types.end(), llvm_argument_types.begin(),
                           [](std::shared_ptr<ir::Type> ir_type) {
                               PRAJNA_ASSERT(ir_type->llvm_type);
                               return ir_type->llvm_type;
                           });
            PRAJNA_ASSERT(ir_function_type->return_type->llvm_type);
            ir_function_type->llvm_type = llvm::FunctionType::get(
                ir_function_type->return_type->llvm_type, llvm_argument_types, false);
            return;
        }
        if (auto ir_pointer_type = cast<ir::PointerType>(ir_type)) {
            PRAJNA_ASSERT(ir_pointer_type->value_type->llvm_type);
            ir_pointer_type->llvm_type =
                llvm::PointerType::get(ir_pointer_type->value_type->llvm_type, 0);
            return;
        }
        if (auto ir_array_type = cast<ir::ArrayType>(ir_type)) {
            PRAJNA_ASSERT(ir_array_type->value_type->llvm_type);
            ir_array_type->llvm_type =
                llvm::ArrayType::get(ir_array_type->value_type->llvm_type, ir_array_type->size);
            return;
        }
        if (auto ir_struct_type = cast<ir::StructType>(ir_type)) {
            auto llvm_struct_type =
                llvm::StructType::create(static_llvm_context, ir_struct_type->fullname);
            ir_struct_type->llvm_type = llvm_struct_type;
            std::vector<llvm::Type*> llvm_types(ir_struct_type->fields.size());
            std::transform(ir_struct_type->fields.begin(), ir_struct_type->fields.end(),
                           llvm_types.begin(), [=](std::shared_ptr<ir::Field> field) {
                               if (!field->type->llvm_type) {
                                   this->emitType(field->type);
                               }
                               PRAJNA_ASSERT(field->type->llvm_type);
                               return field->type->llvm_type;
                           });
            llvm_struct_type->setBody(llvm_types, true);

            return;
        }

        if (auto ir_null_type = cast<ir::NullType>(ir_type)) {
            return;
        }

        PRAJNA_TODO;
    }

    void emitModule(std::shared_ptr<ir::Module> ir_module, ir::Target ir_target) {
        PRAJNA_ASSERT(!ir_module->llvm_module);
        ir_module->llvm_module = new llvm::Module(ir_module->name, static_llvm_context);
        if (ir_target == ir::Target::nvptx) {
            ir_module->llvm_module->setTargetTriple("nvptx64-nvidia-cuda");
        }

        for (auto ir_global_alloca : ir_module->global_allocas) {
            this->emitGlobalAlloca(ir_global_alloca);
        }

        for (std::shared_ptr<ir::Function> ir_function : ir_module->functions) {
            this->emitFunctionDeclaration(ir_function, ir_target);
            if (ir_function->function_type->annotations.count("kernel")) {
                auto md_node = llvm::MDNode::get(
                    static_llvm_context, {llvm::ValueAsMetadata::get(ir_function->llvm_value),
                                          llvm::MDString::get(static_llvm_context, "kernel"),
                                          llvm::ValueAsMetadata::get(llvm::ConstantInt::get(
                                              llvm::Type::getInt32Ty(static_llvm_context), 1))});
                auto nvvm_annotations_md =
                    ir_module->llvm_module->getOrInsertNamedMetadata("nvvm.annotations");
                nvvm_annotations_md->addOperand(md_node);
            }
        }

        for (std::shared_ptr<ir::Function> ir_function : ir_module->functions) {
            if (not(ir_function->isIntrinsicOrInstructoin() or ir_function->is_declaration)) {
                this->emitFunction(ir_function, ir_target);
            }
        }
    }

    void emitFunctionDeclaration(std::shared_ptr<ir::Function> ir_function, ir::Target ir_target) {
        if (ir_function->function_type->annotations.count("instruction")) {
            return;
        } else if (ir_function->function_type->annotations.count("intrinsic")) {
            PRAJNA_ASSERT(!ir_function->function_type->annotations["intrinsic"].empty());
            auto function_name = ir_function->function_type->annotations["intrinsic"].front();
            PRAJNA_ASSERT(ir_function->function_type->llvm_type);
            llvm::FunctionType* llvm_fun_type =
                static_cast<llvm::FunctionType*>(ir_function->function_type->llvm_type);
            llvm::Function* llvm_fun =
                llvm::Function::Create(llvm_fun_type, llvm::Function::ExternalLinkage,
                                       function_name, ir_function->parent_module->llvm_module);
            ir_function->llvm_value = llvm_fun;
        } else {
            auto function_fullname = ir_target == ir::Target::nvptx
                                         ? mangleNvvmName(ir_function->fullname)
                                         : ir_function->fullname;

            PRAJNA_ASSERT(ir_function->function_type->llvm_type);
            llvm::FunctionType* llvm_fun_type =
                static_cast<llvm::FunctionType*>(ir_function->function_type->llvm_type);
            llvm::Function* llvm_fun =
                llvm::Function::Create(llvm_fun_type, llvm::Function::ExternalLinkage,
                                       function_fullname, ir_function->parent_module->llvm_module);
            ir_function->llvm_value = llvm_fun;
        }
    }

    void emitFunction(std::shared_ptr<ir::Function> ir_function, ir::Target ir_target) {
        llvm::Function* llvm_fun = static_cast<llvm::Function*>(ir_function->llvm_value);
        PRAJNA_ASSERT(llvm_fun);
        PRAJNA_ASSERT(ir_function->arguments.size() == llvm_fun->arg_size());
        size_t i = 0;
        for (auto llvm_arg = llvm_fun->arg_begin(); llvm_arg != llvm_fun->arg_end();
             ++llvm_arg, ++i) {
            ir_function->arguments[i]->llvm_value = llvm_arg;
        }

        for (auto block : ir_function->blocks) {
            emitBlock(block, ir_target);
        }
    }

    void emitBlock(std::shared_ptr<ir::Block> ir_block, ir::Target ir_target) {
        PRAJNA_ASSERT(ir_block && ir_block->parent_function);

        if (ir_block->llvm_value != nullptr) {
            return;
        }

        PRAJNA_ASSERT(ir_block->parent_function->llvm_value);
        ir_block->llvm_value = llvm::BasicBlock::Create(
            static_llvm_context, "",
            static_cast<llvm::Function*>(ir_block->parent_function->llvm_value), nullptr);

        for (auto ir_value : ir_block->values) {
            emitValue(ir_value, ir_target);
        }
    }

    void emitValue(std::shared_ptr<ir::Value> ir_value, ir::Target ir_target) {
        if (is<ir::Argument>(ir_value) || is<ir::Function>(ir_value)) {
            return;
        }

        if (auto ir_constant = cast<ir::Constant>(ir_value)) {
            emitConstant(ir_constant, ir_target);
            return;
        }

        PRAJNA_ASSERT(ir_value->llvm_value == nullptr);

        if (auto ir_instruction = cast<ir::Instruction>(ir_value)) {
            emitInstruction(ir_instruction, ir_target);
            return;
        }

        if (auto ir_null_value = cast<ir::VoidValue>(ir_value)) {
            ir_null_value->llvm_value = nullptr;
            return;
        }

        PRAJNA_ASSERT(false, ir_value->tag);
    }

    void emitConstant(std::shared_ptr<ir::Constant> ir_constant, ir::Target ir_target) {
        if (ir_constant->llvm_value) {
            return;
        }

        if (auto ir_constant_char = cast<ir::ConstantChar>(ir_constant)) {
            PRAJNA_ASSERT(ir_constant_char->type->llvm_type);
            ir_constant_char->llvm_value =
                llvm::ConstantInt::get(ir_constant_char->type->llvm_type, ir_constant_char->value);
            return;
        }
        if (auto ir_constant_bool = cast<ir::ConstantBool>(ir_constant)) {
            PRAJNA_ASSERT(ir_constant_bool->type->llvm_type);
            ir_constant_bool->llvm_value =
                llvm::ConstantInt::get(ir_constant_bool->type->llvm_type, ir_constant_bool->value);
            return;
        }
        if (auto ir_constant_int = cast<ir::ConstantInt>(ir_constant)) {
            PRAJNA_ASSERT(ir_constant_int->type->llvm_type);
            ir_constant_int->llvm_value =
                llvm::ConstantInt::get(ir_constant_int->type->llvm_type, ir_constant_int->value);
            return;
        }
        if (auto ir_constant_float = cast<ir::ConstantFloat>(ir_constant)) {
            PRAJNA_ASSERT(ir_constant_float->type->llvm_type);
            ir_constant_float->llvm_value =
                llvm::ConstantFP::get(ir_constant_float->type->llvm_type, ir_constant_float->value);
            return;
        }
        if (auto ir_constant_array = cast<ir::ConstantArray>(ir_constant)) {
            std::vector<llvm::Constant*> llvm_contants(
                ir_constant_array->initialize_constants.size());
            std::transform(RANGE(ir_constant_array->initialize_constants), llvm_contants.begin(),
                           [=](auto ir_init) {
                               auto llvm_constant =
                                   static_cast<llvm::Constant*>(ir_init->llvm_value);
                               PRAJNA_ASSERT(llvm_constant);
                               return llvm_constant;
                           });
            PRAJNA_ASSERT(ir_constant_array->type->llvm_type);
            ir_constant_array->llvm_value = llvm::ConstantArray::get(
                static_cast<llvm::ArrayType*>(ir_constant_array->type->llvm_type), llvm_contants);
            return;
        }

        PRAJNA_TODO;
    }

    void emitCallInstructionAsIntrinsic(std::shared_ptr<ir::Call> ir_call, ir::Target ir_target) {
        auto llvm_basic_block = static_cast<llvm::BasicBlock*>(ir_call->parent_block->llvm_value);
        PRAJNA_ASSERT(llvm_basic_block);
        auto ir_function = cast<ir::Function>(ir_call->function());
        auto annotations_instruction = ir_function->function_type->annotations["instruction"];
        PRAJNA_ASSERT(annotations_instruction.size() > 0);
        auto category = annotations_instruction[0];

        if (category == "ICmp" || category == "FCmp") {
            PRAJNA_ASSERT(annotations_instruction.size() == 2);
            PRAJNA_ASSERT(ir_call->argumentSize() == 2);
            auto ir_lhs_type = cast<ir::PointerType>(ir_call->argument(0)->type);
            PRAJNA_ASSERT(ir_lhs_type->value_type->llvm_type);
            PRAJNA_ASSERT(ir_call->argument(0)->llvm_value);
            auto llvm_lhs_value =
                new llvm::LoadInst(ir_lhs_type->value_type->llvm_type,
                                   ir_call->argument(0)->llvm_value, "", llvm_basic_block);
            auto llvm_rhs_value = ir_call->argument(1)->llvm_value;
            PRAJNA_ASSERT(llvm_rhs_value);

            std::map<std::string, llvm::CmpInst::OtherOps> cmp_inst_other_ops = {
                {"ICmp", llvm::CmpInst::OtherOps::ICmp}, {"FCmp", llvm::CmpInst::OtherOps::FCmp}};

            std::map<std::string, llvm::ICmpInst::Predicate> icmp_inst_predicate_dict = {
                {"FCMP_FALSE", llvm::CmpInst::Predicate::FCMP_FALSE},
                {"FCMP_OEQ", llvm::CmpInst::Predicate::FCMP_OEQ},
                {"FCMP_OGT", llvm::CmpInst::Predicate::FCMP_OGT},
                {"FCMP_OGE", llvm::CmpInst::Predicate::FCMP_OGE},
                {"FCMP_OLT", llvm::CmpInst::Predicate::FCMP_OLT},
                {"FCMP_OLE", llvm::CmpInst::Predicate::FCMP_OLE},
                {"FCMP_ONE", llvm::CmpInst::Predicate::FCMP_ONE},
                {"FCMP_ORD", llvm::CmpInst::Predicate::FCMP_ORD},
                {"FCMP_UNO", llvm::CmpInst::Predicate::FCMP_UNO},
                {"FCMP_UEQ", llvm::CmpInst::Predicate::FCMP_UEQ},
                {"FCMP_UGT", llvm::CmpInst::Predicate::FCMP_UGT},
                {"FCMP_UGE", llvm::CmpInst::Predicate::FCMP_UGE},
                {"FCMP_ULT", llvm::CmpInst::Predicate::FCMP_ULT},
                {"FCMP_ULE", llvm::CmpInst::Predicate::FCMP_ULE},
                {"FCMP_UNE", llvm::CmpInst::Predicate::FCMP_UNE},
                {"FCMP_TRUE", llvm::CmpInst::Predicate::FCMP_TRUE},
                // integer
                {"ICMP_EQ", llvm::CmpInst::Predicate::ICMP_EQ},
                {"ICMP_NE", llvm::CmpInst::Predicate::ICMP_NE},
                {"ICMP_UGT", llvm::CmpInst::Predicate::ICMP_UGT},
                {"ICMP_UGE", llvm::CmpInst::Predicate::ICMP_UGE},
                {"ICMP_ULT", llvm::CmpInst::Predicate::ICMP_ULT},
                {"ICMP_ULE", llvm::CmpInst::Predicate::ICMP_ULE},
                {"ICMP_SGT", llvm::CmpInst::Predicate::ICMP_SGT},
                {"ICMP_SGE", llvm::CmpInst::Predicate::ICMP_SGE},
                {"ICMP_SLT", llvm::CmpInst::Predicate::ICMP_SLT},
                {"ICMP_SLE", llvm::CmpInst::Predicate::ICMP_SLE},
            };

            auto annotation_predicate = annotations_instruction[1];
            PRAJNA_ASSERT(cmp_inst_other_ops.count(category));
            PRAJNA_ASSERT(icmp_inst_predicate_dict.count(annotation_predicate));
            ir_call->llvm_value = llvm::CmpInst::Create(
                cmp_inst_other_ops[category], icmp_inst_predicate_dict[annotation_predicate],
                llvm_lhs_value, llvm_rhs_value, "", llvm_basic_block);
            return;
        }
        if (category == "BinaryOperator") {
            PRAJNA_ASSERT(annotations_instruction.size() == 2);

            PRAJNA_ASSERT(ir_call->argumentSize() == 2);
            auto ir_lhs_type = cast<ir::PointerType>(ir_call->argument(0)->type);
            PRAJNA_ASSERT(ir_lhs_type->value_type->llvm_type);
            PRAJNA_ASSERT(ir_call->argument(0)->llvm_value);
            auto llvm_lhs_value =
                new llvm::LoadInst(ir_lhs_type->value_type->llvm_type,
                                   ir_call->argument(0)->llvm_value, "", llvm_basic_block);
            auto llvm_rhs_value = ir_call->argument(1)->llvm_value;
            PRAJNA_ASSERT(llvm_rhs_value);

            std::map<std::string, llvm::BinaryOperator::BinaryOps> binary_operator_dict = {
                {"Add", llvm::BinaryOperator::BinaryOps::Add},
                {"Sub", llvm::BinaryOperator::BinaryOps::Sub},
                {"Mul", llvm::BinaryOperator::BinaryOps::Mul},
                {"SDiv", llvm::BinaryOperator::BinaryOps::SDiv},
                {"UDiv", llvm::BinaryOperator::BinaryOps::UDiv},
                {"SRem", llvm::BinaryOperator::BinaryOps::SRem},
                {"URem", llvm::BinaryOperator::BinaryOps::URem},
                {"And", llvm::BinaryOperator::BinaryOps::And},
                {"Or", llvm::BinaryOperator::BinaryOps::Or},
                {"Shl", llvm::BinaryOperator::BinaryOps::Shl},
                {"LShr", llvm::BinaryOperator::BinaryOps::LShr},
                {"AShr", llvm::BinaryOperator::BinaryOps::AShr},
                {"Xor", llvm::BinaryOperator::BinaryOps::Xor},
                {"Xor", llvm::BinaryOperator::BinaryOps::Xor},
                {"Xor", llvm::BinaryOperator::BinaryOps::Xor},
                {"FAdd", llvm::BinaryOperator::BinaryOps::FAdd},
                {"FSub", llvm::BinaryOperator::BinaryOps::FSub},
                {"FMul", llvm::BinaryOperator::BinaryOps::FMul},
                {"FDiv", llvm::BinaryOperator::BinaryOps::FDiv},
                {"FRem", llvm::BinaryOperator::BinaryOps::FRem},
            };

            auto annotation_operator = annotations_instruction[1];
            PRAJNA_ASSERT(binary_operator_dict.count(annotation_operator));
            ir_call->llvm_value =
                llvm::BinaryOperator::Create(binary_operator_dict[annotation_operator],
                                             llvm_lhs_value, llvm_rhs_value, "", llvm_basic_block);
            return;
        }
        if (category == "CastInst") {
            auto ir_lhs_type = cast<ir::PointerType>(ir_call->argument(0)->type);
            PRAJNA_ASSERT(ir_lhs_type->value_type->llvm_type);
            PRAJNA_ASSERT(ir_call->argument(0)->llvm_value);
            auto llvm_lhs_value =
                new llvm::LoadInst(ir_lhs_type->value_type->llvm_type,
                                   ir_call->argument(0)->llvm_value, "", llvm_basic_block);

            std::map<std::string, llvm::CastInst::CastOps> cast_operator_dict = {
                {"Trunc", llvm::CastInst::Trunc},
                {"ZExt", llvm::CastInst::ZExt},
                {"SExt", llvm::CastInst::SExt},
                {"FPToUI", llvm::CastInst::FPToUI},
                {"FPToSI", llvm::CastInst::FPToSI},
                {"UIToFP", llvm::CastInst::UIToFP},
                {"SIToFP", llvm::CastInst::SIToFP},
                {"FPTrunc", llvm::CastInst::FPTrunc},
                {"FPExt", llvm::CastInst::FPExt},
                {"PtrToInt", llvm::CastInst::PtrToInt},
                {"IntToPtr", llvm::CastInst::IntToPtr},
                {"BitCast", llvm::CastInst::BitCast},
                {"AddrSpaceCast", llvm::CastInst::AddrSpaceCast},
            };

            auto annotation_type = annotations_instruction[2];
            auto iter_type = std::find_if(RANGE(ir::global_context.created_types),
                                          [=](std::shared_ptr<ir::Type> ir_type) {
                                              return ir_type->name == annotation_type;
                                          });
            PRAJNA_ASSERT(iter_type != ir::global_context.created_types.end());
            auto ir_cast_type = *iter_type;

            PRAJNA_ASSERT(annotations_instruction.size() == 3);
            auto annotation_operator = annotations_instruction[1];
            PRAJNA_ASSERT(cast_operator_dict.count(annotation_operator));
            PRAJNA_ASSERT(ir_call->argumentSize() == 1);
            ir_call->llvm_value =
                llvm::CastInst::Create(cast_operator_dict[annotation_operator], llvm_lhs_value,
                                       ir_cast_type->llvm_type, "", llvm_basic_block);
            return;
        }

        PRAJNA_UNREACHABLE;
        return;
    };

    void emitGlobalAlloca(sp<ir::GlobalAlloca> ir_global_alloca) {
        auto ir_value_type = cast<ir::PointerType>(ir_global_alloca->type)->value_type;
        PRAJNA_ASSERT(ir_value_type && ir_value_type->llvm_type);
        PRAJNA_ASSERT(ir_global_alloca->parent_module->llvm_module);
        // 事实上llvm::GlobalVariable其实获取一个个指针
        auto llvm_global_variable = new llvm::GlobalVariable(
            *(ir_global_alloca->parent_module->llvm_module), ir_value_type->llvm_type, false,
            llvm::GlobalValue::LinkageTypes::ExternalLinkage, nullptr, ir_global_alloca->fullname);
        if (!ir_global_alloca->is_external) {
            // @note 需要初始化, 否则符号会找到不到. 也就是说如果不初始化, 则其为external
            llvm_global_variable->setInitializer(llvm::UndefValue::get(ir_value_type->llvm_type));
        }
        ir_global_alloca->llvm_value = llvm_global_variable;
    }

    void emitInstruction(std::shared_ptr<ir::Instruction> ir_instruction, ir::Target ir_target) {
        // PRAJNA_ASSERT(ir_instruction->llvm_value == nullptr);

        auto llvm_basic_block =
            static_cast<llvm::BasicBlock*>(ir_instruction->parent_block->llvm_value);
        PRAJNA_ASSERT(llvm_basic_block);
        if (auto ir_call = cast<ir::Call>(ir_instruction)) {
            auto ir_function_type = ir_call->function()->getFunctionType();
            PRAJNA_ASSERT(ir_function_type);
            if (ir_function_type->annotations.count("instruction")) {
                return this->emitCallInstructionAsIntrinsic(ir_call, ir_target);
            } else {
                std::vector<llvm::Value*> llvm_arguments(ir_call->argumentSize());
                for (size_t i = 0; i < llvm_arguments.size(); ++i) {
                    llvm_arguments[i] = ir_call->argument(i)->llvm_value;
                    PRAJNA_ASSERT(llvm_arguments[i]);
                }
                PRAJNA_ASSERT(ir_call->function()->getFunctionType()->llvm_type);
                PRAJNA_ASSERT(ir_call->function()->llvm_value);
                ir_call->llvm_value = llvm::CallInst::Create(
                    static_cast<llvm::FunctionType*>(
                        ir_call->function()->getFunctionType()->llvm_type),
                    ir_call->function()->llvm_value, llvm_arguments, "", llvm_basic_block);
                return;
            }
            return;
        }
        if (auto ir_return = cast<ir::Return>(ir_instruction)) {
            auto llvm_return = llvm::ReturnInst::Create(
                static_llvm_context, ir_return->value()->llvm_value, llvm_basic_block);
            return;
        }
        if (auto ir_alloca = cast<ir::Alloca>(ir_instruction)) {
            // Align需要设置一个合理的值, 目前先设置为8
            // PRAJNA_ASSERT()
            auto ir_alloca_type = cast<ir::PointerType>(ir_alloca->type);
            PRAJNA_ASSERT(ir_alloca_type && ir_alloca_type->value_type->llvm_type);
            ir_alloca->llvm_value = new llvm::AllocaInst(ir_alloca_type->value_type->llvm_type, 0,
                                                         ir_alloca->name, llvm_basic_block);
            return;
        }
        if (auto ir_global_alloca = cast<ir::GlobalAlloca>(ir_instruction)) {
            PRAJNA_UNREACHABLE;
        }
        if (auto ir_load_pointer = cast<ir::LoadPointer>(ir_instruction)) {
            PRAJNA_ASSERT(ir_load_pointer->type->llvm_type);
            PRAJNA_ASSERT(ir_load_pointer->pointer()->llvm_value);
            auto llvm_load_ptr =
                new llvm::LoadInst(ir_load_pointer->type->llvm_type,
                                   ir_load_pointer->pointer()->llvm_value, "", llvm_basic_block);
            ir_load_pointer->llvm_value = llvm_load_ptr;
            return;
        }
        if (auto ir_store_pointer = cast<ir::StorePointer>(ir_instruction)) {
            PRAJNA_ASSERT(ir_store_pointer->value()->llvm_value);
            PRAJNA_ASSERT(ir_store_pointer->pointer()->llvm_value);

            auto llvm_store_ptr =
                new llvm::StoreInst(ir_store_pointer->value()->llvm_value,
                                    ir_store_pointer->pointer()->llvm_value, "", llvm_basic_block);
            ir_store_pointer->llvm_value = llvm_store_ptr;
            return;
        }
        if (auto ir_condition_branch = cast<ir::ConditionBranch>(ir_instruction)) {
            // 需要处理, 因为true/falseBlock不会加入到其他Block里
            this->emitBlock(ir_condition_branch->trueBlock(), ir_target);
            this->emitBlock(ir_condition_branch->falseBlock(), ir_target);
            PRAJNA_ASSERT(ir_condition_branch->trueBlock()->llvm_value);
            PRAJNA_ASSERT(ir_condition_branch->falseBlock()->llvm_value);
            PRAJNA_ASSERT(ir_condition_branch->condition()->llvm_value);
            ir_condition_branch->llvm_value = llvm::BranchInst::Create(
                static_cast<llvm::BasicBlock*>(ir_condition_branch->trueBlock()->llvm_value),
                static_cast<llvm::BasicBlock*>(ir_condition_branch->falseBlock()->llvm_value),
                ir_condition_branch->condition()->llvm_value, llvm_basic_block);
            return;
        }
        if (auto ir_jump_branch = cast<ir::JumpBranch>(ir_instruction)) {
            PRAJNA_ASSERT(ir_jump_branch->parent_block->parent_function ==
                          ir_jump_branch->nextBlock()->parent_function);

            this->emitBlock(ir_jump_branch->nextBlock(), ir_target);
            PRAJNA_ASSERT(ir_jump_branch->nextBlock()->llvm_value);
            ir_jump_branch->llvm_value = llvm::BranchInst::Create(
                static_cast<llvm::BasicBlock*>(ir_jump_branch->nextBlock()->llvm_value),
                llvm_basic_block);
            return;
        }
        if (auto ir_get_struct_element_pointer =
                cast<ir::GetStructElementPointer>(ir_instruction)) {
            // @todo 后续需要进一步处理, 看一下偏移地址的类型是否可以一直是64位的, 还是需要调整
            std::vector<llvm::Value*> llvm_idx_list(2);
            llvm_idx_list[0] =
                llvm::ConstantInt::get(llvm::Type::getInt64Ty(static_llvm_context), 0);
            // @warning 结构体的偏移下标必须使用32位整型
            llvm_idx_list[1] = llvm::ConstantInt::get(llvm::Type::getInt32Ty(static_llvm_context),
                                                      ir_get_struct_element_pointer->field->index);

            auto ir_pointer_type =
                cast<ir::PointerType>(ir_get_struct_element_pointer->pointer()->type);
            PRAJNA_ASSERT(ir_pointer_type && ir_pointer_type->value_type->llvm_type);
            PRAJNA_ASSERT(ir_get_struct_element_pointer->pointer()->llvm_value);
            ir_get_struct_element_pointer->llvm_value = llvm::GetElementPtrInst::Create(
                ir_pointer_type->value_type->llvm_type,
                ir_get_struct_element_pointer->pointer()->llvm_value, llvm_idx_list, "",
                llvm_basic_block);
            return;
        }
        if (auto ir_get_array_element_pointer = cast<ir::GetArrayElementPointer>(ir_instruction)) {
            std::vector<llvm::Value*> llvm_idx_list(2);
            llvm_idx_list[0] =
                llvm::ConstantInt::get(llvm::Type::getInt64Ty(static_llvm_context), 0);
            llvm_idx_list[1] = ir_get_array_element_pointer->index()->llvm_value;
            auto ir_pointer_type =
                cast<ir::PointerType>(ir_get_array_element_pointer->pointer()->type);
            PRAJNA_ASSERT(ir_pointer_type && ir_pointer_type->value_type->llvm_type);
            PRAJNA_ASSERT(ir_get_array_element_pointer->pointer()->llvm_value);
            ir_get_array_element_pointer->llvm_value =
                llvm::GetElementPtrInst::Create(ir_pointer_type->value_type->llvm_type,
                                                ir_get_array_element_pointer->pointer()->llvm_value,
                                                llvm_idx_list, "", llvm_basic_block);
            return;
        }
        if (auto ir_get_pointer_element_pointer =
                cast<ir::GetPointerElementPointer>(ir_instruction)) {
            std::vector<llvm::Value*> llvm_idx_list(1);
            llvm_idx_list[0] = ir_get_pointer_element_pointer->index()->llvm_value;
            PRAJNA_ASSERT(ir_get_pointer_element_pointer->type->llvm_type);
            PRAJNA_ASSERT(ir_get_pointer_element_pointer->pointer()->llvm_value);
            auto llvm_pointer = new llvm::LoadInst(
                ir_get_pointer_element_pointer->type->llvm_type,
                ir_get_pointer_element_pointer->pointer()->llvm_value, "", llvm_basic_block);
            auto ir_pointer_type = cast<ir::PointerType>(ir_get_pointer_element_pointer->type);
            PRAJNA_ASSERT(ir_pointer_type && ir_pointer_type->value_type->llvm_type);
            ir_get_pointer_element_pointer->llvm_value =
                llvm::GetElementPtrInst::Create(ir_pointer_type->value_type->llvm_type,
                                                llvm_pointer, llvm_idx_list, "", llvm_basic_block);
            return;
        }
        if (auto ir_bit_cast = cast<ir::BitCast>(ir_instruction)) {
            PRAJNA_ASSERT(ir_bit_cast->value()->llvm_value);
            PRAJNA_ASSERT(ir_bit_cast->type->llvm_type);
            ir_bit_cast->llvm_value =
                new llvm::BitCastInst(ir_bit_cast->value()->llvm_value,
                                      ir_bit_cast->type->llvm_type, "", llvm_basic_block);
            return;
        }

        PRAJNA_ASSERT(false, ir_instruction->tag);
    }
};

std::shared_ptr<ir::Module> llvmCodegen(std::shared_ptr<ir::Module> ir_module,
                                        ir::Target ir_target) {
    auto llvm_codegen = LlvmCodegen::create();

    // emit type
    for (auto type : ir::global_context.created_types) {
        llvm_codegen->emitType(type);
    }

    llvm_codegen->emitModule(ir_module, ir_target);

#ifdef PRAJNA_ENABLE_LLVM_DUMP
    ir_module->llvm_module->dump();
#endif

#ifdef PRAJNA_ENABLE_LLVM_VERIFY
    llvm::verifyModule(*ir_module->llvm_module, &llvm::dbgs());
#endif

    for (auto [ir_target, ir_sub_module] : ir_module->modules) {
        if (ir_sub_module == nullptr) continue;

        // 如果没有核函数, 则不生成. 因为不会被使用, gpu会把所用的的ir都拷贝过去
        if (std::none_of(RANGE(ir_sub_module->functions),
                         [](std::shared_ptr<ir::Function> ir_function) {
                             return ir_function->function_type->annotations.count("kernel");
                         })) {
            continue;
        }

        llvmCodegen(ir_sub_module, ir_target);
    }

    return ir_module;
}

}  // namespace prajna::codegen
