#pragma once

#include <any>
#include <functional>
#include <list>
#include <memory>
#include <set>
#include <string>
#include <unordered_set>
#include <vector>

#include "boost/multiprecision/cpp_bin_float.hpp"
#include "boost/multiprecision/cpp_int.hpp"
#include "boost/noncopyable.hpp"
#include "prajna/ast/ast.hpp"
#include "prajna/helper.hpp"
#include "prajna/ir/cloner.hpp"
#include "prajna/ir/global_context.h"
#include "prajna/ir/type.hpp"

namespace llvm {
class Module;
}

namespace prajna::lowering {

class SymbolTable;

}

namespace prajna::ir {

enum struct Target { none, host, nvptx };

inline std::string targetToString(Target ir_target) {
    switch (ir_target) {
        case Target::none:
            PRAJNA_UNREACHABLE;
            return "";
        case Target::host:
            return "host";
        case Target::nvptx:
            return "nvptx";
    }

    return "";
}

inline Target stringToTarget(std::string str_target) {
    if (str_target == "host") return Target::host;
    if (str_target == "nvptx") return Target::nvptx;

    PRAJNA_UNREACHABLE;
    return Target::none;
}

class Instruction;

struct InstructionWithOperandIndex {
    std::shared_ptr<Instruction> instruction;
    size_t operand_index;
};

inline bool operator==(prajna::ir::InstructionWithOperandIndex lhs,
                       prajna::ir::InstructionWithOperandIndex rhs) {
    return lhs.instruction == rhs.instruction && lhs.operand_index == rhs.operand_index;
}

}  // namespace prajna::ir

template <>
struct std::hash<prajna::ir::InstructionWithOperandIndex> {
    std::size_t operator()(prajna::ir::InstructionWithOperandIndex inst_with_idx) const noexcept {
        std::size_t h1 =
            std::hash<std::shared_ptr<prajna::ir::Instruction>>{}(inst_with_idx.instruction);
        std::size_t h2 = std::hash<size_t>{}(inst_with_idx.operand_index);
        return h1 ^ (h2 << 1);  // or use boost::hash_combine
    }
};

namespace llvm {

class Value;
class Module;

}  // namespace llvm

namespace prajna::ir {

class Block;
class Function;
class Module;

class Value : public Named, public std::enable_shared_from_this<Value> {
   protected:
    Value() {}

    Value(const Value& other) {
        this->type = other.type;
        this->annotations = other.annotations;
        this->tag = other.tag;

        this->name = other.name;
        this->fullname = other.fullname;

        this->parent_block = nullptr;
        this->instruction_with_index_list.clear();
        this->llvm_value = nullptr;
    }

   public:
    static std::shared_ptr<Value> create(std::shared_ptr<Type> ir_type) {
        std::shared_ptr<Value> self(new Value);
        self->type = ir_type;
        self->tag = "Value";
        return self;
    }

    virtual ~Value() {}

    /// @brief 释放不必要的依赖, 解除循环引用
    virtual void detach() {
        // 只是解除依赖, 不是销毁数据,
        this->instruction_with_index_list.clear();
        this->parent_block = nullptr;
    }

    virtual void finalize() { this->detach(); }

    std::shared_ptr<Function> getParentFunction();

    std::shared_ptr<FunctionType> getFunctionType() {
        if (auto ir_pointer_type = cast<PointerType>(this->type)) {
            if (auto ir_function_type = cast<FunctionType>(ir_pointer_type->value_type)) {
                return ir_function_type;
            }
        }

        return nullptr;
    }

    std::shared_ptr<Block> getRootBlock();

    bool isFunction() { return getFunctionType() != nullptr; }

    virtual std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) {
        PRAJNA_UNIMPLEMENT;
        return nullptr;
    }

   public:
    std::shared_ptr<Type> type = nullptr;

    // std::set<std::string> annotations;
    std::map<std::string, std::vector<std::string>> annotations;

    // 最后需要释放以解除智能指针的引用计数
    std::shared_ptr<Block> parent_block = nullptr;
    std::list<InstructionWithOperandIndex> instruction_with_index_list;

    ast::SourceLocation source_location;

    // 用于llvm的codegen, 仅引用, 不管理内存
    llvm::Value* llvm_value = nullptr;

    // 用于方便调试, 否则无法有效辨别他们
    std::string tag = "";
};

class VoidValue : public Value {
   protected:
    VoidValue() = default;

   public:
    static std::shared_ptr<VoidValue> create() {
        std::shared_ptr<VoidValue> self(new VoidValue);
        self->type = VoidType::create();
        self->tag = "VoidValue";
        return self;
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<VoidValue> ir_new(new VoidValue(*this));
        return ir_new;
    }
};

class Argument : public Value {
   protected:
    Argument() = default;

   public:
    static std::shared_ptr<Argument> create(std::shared_ptr<Type> ir_type) {
        std::shared_ptr<Argument> self(new Argument);
        self->type = ir_type;
        self->tag = "Argument";
        return self;
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<Argument> ir_new(new Argument(*this));
        return ir_new;
    }
};

class Constant : public Value {
   protected:
    Constant() = default;

   public:
};

class ConstantBool : public Constant {
   protected:
    ConstantBool() = default;

   public:
    static std::shared_ptr<ConstantBool> create(bool value) {
        std::shared_ptr<ConstantBool> self(new ConstantBool);
        self->type = BoolType::create();
        self->value = value;
        self->tag = "ConstantBool";
        return self;
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<ConstantBool> ir_new(new ConstantBool(*this));
        return ir_new;
    }

   public:
    bool value;
};

class ConstantRealNumber : public Constant {
   protected:
    ConstantRealNumber() = default;
};

class ConstantInt : public ConstantRealNumber {
   protected:
    ConstantInt() = default;

   public:
    static std::shared_ptr<ConstantInt> create(std::shared_ptr<Type> type, int64_t value) {
        std::shared_ptr<ConstantInt> self(new ConstantInt);
        self->type = type;
        self->value = value;
        self->tag = "ConstantInt";
        return self;
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<ConstantInt> ir_new(new ConstantInt(*this));
        return ir_new;
    }

   public:
    int64_t value;
};

class ConstantFloat : public Constant {
   protected:
    ConstantFloat() = default;

   public:
    static std::shared_ptr<ConstantFloat> create(std::shared_ptr<Type> type, double value) {
        std::shared_ptr<ConstantFloat> self(new ConstantFloat);
        self->type = type;
        self->value = value;
        self->tag = "ConstantFloat";
        return self;
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<ConstantFloat> ir_new(new ConstantFloat(*this));
        return ir_new;
    }

   public:
    double value;
};

class ConstantChar : public Constant {
   protected:
    ConstantChar() = default;

   public:
    static std::shared_ptr<ConstantChar> create(char value) {
        std::shared_ptr<ConstantChar> self(new ConstantChar);
        self->type = CharType::create();
        self->value = value;
        self->tag = "ConstantChar";
        return self;
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<ConstantChar> ir_new(new ConstantChar(*this));
        return ir_new;
    }

   public:
    char value;
};

class ConstantNull : public Constant {
   protected:
    ConstantNull() = default;

   public:
    static std::shared_ptr<ConstantNull> create() {
        std::shared_ptr<ConstantNull> self(new ConstantNull);
        self->type = PointerType::create(nullptr);
        self->tag = "ConstantNull";
        return self;
    }
};

class ConstantArray : public Constant {
   protected:
    ConstantArray() = default;

   public:
    static std::shared_ptr<ConstantArray> create(
        std::shared_ptr<ArrayType> ir_array_type,
        std::vector<std::shared_ptr<Constant>> ir_init_constants) {
        std::shared_ptr<ConstantArray> self(new ConstantArray);
        self->tag = "ConstantArray";
        self->type = ir_array_type;
        self->initialize_constants = ir_init_constants;
        return self;
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<ConstantArray> ir_new(new ConstantArray(*this));
        ;

        for (size_t i = 0; i < initialize_constants.size(); ++i) {
            ir_new->initialize_constants.push_back(
                cast<Constant>(initialize_constants[i]->clone(function_cloner)));
        }

        return ir_new;
    }

    std::vector<std::shared_ptr<Constant>> initialize_constants;
};

class ConstantStruct : public Constant {
   protected:
    ConstantStruct() = default;

   public:
    static std::shared_ptr<ConstantStruct> create(
        std::shared_ptr<Type> type, std::map<std::string, std::shared_ptr<Constant>> fields) {
        std::shared_ptr<ConstantStruct> self(new ConstantStruct);
        self->type = type;
        self->fileds = fields;
        self->tag = "ConstantStruct";
        return self;
    };

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<ConstantStruct> ir_new(new ConstantStruct(*this));
        return ir_new;
    }

   public:
    std::map<std::string, std::shared_ptr<Constant>> fileds;
};

class Block : public Value {
   protected:
    Block() = default;

   public:
    using iterator = std::list<std::shared_ptr<Value>>::iterator;

    static std::shared_ptr<Block> create() {
        std::shared_ptr<Block> self(new Block);
        auto p = self->shared_from_this();
        self->type = nullptr;
        self->tag = "Block";
        return self;
    }

    std::shared_ptr<Function> getParentFunction() {
        if (this->parent_block) {
            return this->parent_block->getParentFunction();
        } else {
            PRAJNA_ASSERT(parent_function);
            return parent_function;
        }
    }

    iterator insert(iterator iter, std::shared_ptr<Value> ir_value) {
        ir_value->parent_block = cast<Block>(this->shared_from_this());
        return this->values.insert(iter, ir_value);
    }

    iterator find(std::shared_ptr<Value> ir_value) {
        PRAJNA_ASSERT(ir_value->parent_block.get() == this);
        return std::find(RANGE(this->values), ir_value);
    }

    iterator erase(iterator iter) {
        PRAJNA_ASSERT((*iter) && (*iter)->parent_block.get() == this);
        (*iter)->parent_block = nullptr;
        return this->values.erase(iter);
    }

    void remove(std::shared_ptr<Value> ir_value) {
        ir_value->parent_block = nullptr;
        this->values.erase(std::find(RANGE(this->values), ir_value));
    }

    void pushFront(std::shared_ptr<Value> ir_value) {
        ir_value->parent_block = cast<Block>(this->shared_from_this());
        this->values.push_front(ir_value);
    }

    void pushBack(std::shared_ptr<Value> ir_value) {
        ir_value->parent_block = cast<Block>(this->shared_from_this());
        this->values.push_back(ir_value);
    }

    void finalize() override {
        Value::finalize();
        this->values.clear();
    }

    void detach() override {
        Value::detach();
        this->parent_function = nullptr;
    }

    virtual std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<Block> ir_new(new Block(*this));
        ir_new->values.clear();

        for (auto ir_value : values) {
            //在Function::clone里已经处理过了
            if (!is<Argument>(ir_value)) {
                auto ir_new_value = ir_value->clone(function_cloner);
                // PRAJNA_ASSERT(function_cloner->value_dict.count(ir_value) == 0);
                function_cloner->value_dict[ir_value] = ir_new_value;
            } else {
                PRAJNA_ASSERT(function_cloner->value_dict.count(ir_value));
            }
            ir_new->pushBack(function_cloner->value_dict[ir_value]);
        }

        return ir_new;
    }

   public:
    std::list<std::shared_ptr<Value>> values;
    std::shared_ptr<Function> parent_function = nullptr;
};

class Function : public Value {
   protected:
    Function() = default;

   public:
    static std::shared_ptr<Function> create(std::shared_ptr<FunctionType> function_type) {
        std::shared_ptr<Function> self(new Function);
        self->function_type = function_type;
        // @warning 事实上llvm::Function是一个指针类型
        self->type = PointerType::create(function_type);
        self->tag = "Function";
        return self;
    }

    bool isIntrinsicOrInstructoin() {
        return (this->function_type->annotations.count("intrinsic")) ||
               (this->function_type->annotations.count("instruction"));
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<Function> ir_new(new Function(*this));
        ir_new->parent_module = function_cloner->module;
        function_cloner->value_dict[shared_from_this()] = ir_new;

        ir_new->arguments.clear();
        for (size_t i = 0; i < arguments.size(); ++i) {
            auto ir_new_argument = arguments[i]->clone(function_cloner);
            function_cloner->value_dict[arguments[i]] = ir_new_argument;
            ir_new->arguments.push_back(ir_new_argument);
        }

        // 需要再开头, 因为函数有可能存在递归
        ir_new->blocks.clear();
        for (auto ir_block : blocks) {
            auto ir_new_block = cast<Block>(ir_block->clone(function_cloner));
            ir_new_block->parent_function = ir_new;
            ir_new->blocks.push_back(ir_new_block);
        }

        function_cloner->functions.push_back(ir_new);
        return ir_new;
    }

   public:
    bool is_declaration = false;
    std::shared_ptr<FunctionType> function_type;
    std::vector<std::shared_ptr<Value>> arguments;
    std::list<std::shared_ptr<Block>> blocks;
    std::shared_ptr<Module> parent_module;
};

inline std::shared_ptr<Function> getPropertySetter(std::shared_ptr<Type> ir_type,
                                                   std::string property_name) {
    for (auto [name, ir_function] : ir_type->member_functions) {
        if (ir_function == nullptr) continue;

        auto annotation_property = ir_function->function_type->annotations["property"];
        if (not annotation_property.empty()) {
            PRAJNA_ASSERT(annotation_property.size() == 2);
            if (annotation_property[0] == property_name && annotation_property[1] == "setter") {
                return ir_function;
            }
        }
    }

    return nullptr;
}

inline std::shared_ptr<Function> getPropertyGetter(std::shared_ptr<Type> ir_type,
                                                   std::string property_name) {
    for (auto [name, ir_function] : ir_type->member_functions) {
        if (ir_function == nullptr) continue;

        auto annotation_property = ir_function->function_type->annotations["property"];
        if (not annotation_property.empty()) {
            PRAJNA_ASSERT(annotation_property.size() == 2);
            if (annotation_property[0] == property_name && annotation_property[1] == "getter") {
                return ir_function;
            }
        }
    }

    return nullptr;
}

/// @brief 在lowering时需要用到的辅助IR, 并不应该在lowering后出现
class MemberFunctionWithThisPointer : public Value {
   protected:
    MemberFunctionWithThisPointer() = default;

   public:
    static std::shared_ptr<MemberFunctionWithThisPointer> create(
        std::shared_ptr<Value> ir_this_pointer, std::shared_ptr<Function> ir_global_function) {
        std::shared_ptr<MemberFunctionWithThisPointer> self(new MemberFunctionWithThisPointer);
        self->this_pointer = ir_this_pointer;
        self->function_prototype = ir_global_function;
        self->tag = "MemberFunctionWithThisPointer";
        return self;
    }

    std::shared_ptr<Value> this_pointer;
    std::shared_ptr<Function> function_prototype;
};

class WriteReadAble : virtual public Value {
   protected:
    WriteReadAble() = default;

    bool is_readable = true;
    bool is_writeable = true;
};

class VariableLiked : virtual public WriteReadAble {
   protected:
    VariableLiked() = default;
};

class Variable : public VariableLiked {
   protected:
    Variable() = default;
};

class LocalVariable : public Variable {
   protected:
    LocalVariable() = default;

   public:
    static std::shared_ptr<LocalVariable> create(std::shared_ptr<Type> type) {
        PRAJNA_ASSERT(not is<VoidType>(type));
        std::shared_ptr<LocalVariable> self(new LocalVariable);
        self->type = type;
        self->tag = "LocalVariable";
        return self;
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<LocalVariable> ir_new(new LocalVariable(*this));
        return ir_new;
    }
};

/// @brief

class Instruction : virtual public Value {
   protected:
    Instruction() : Instruction(0) {}

    Instruction(size_t operand_size) { this->operands.resize(operand_size); }

   public:
    virtual void operandResize(size_t size) { return this->operands.resize(size); }

    virtual size_t operandSize() { return this->operands.size(); }

    virtual std::shared_ptr<Value> operand(size_t i) {
        PRAJNA_ASSERT(this->operandSize() > i);
        return this->operands[i];
    };

    virtual void operand(std::shared_ptr<Value> ir_value, size_t i) {
        PRAJNA_ASSERT(this->operandSize() > i);

        auto ir_old_value = this->operands[i];
        if (ir_old_value) {
            ir_old_value->instruction_with_index_list.remove(
                {cast<Instruction>(this->shared_from_this()), i});
        }

        this->operands[i] = ir_value;
        if (ir_value)
            ir_value->instruction_with_index_list.push_back(
                {cast<Instruction>(this->shared_from_this()), i});
    };

    void finalize() override {
        Value::finalize();

        for (size_t i = 0; i < operandSize(); ++i) {
            this->operand(nullptr, i);
        }

        this->operandResize(0);
    }

    void cloneOperands(std::shared_ptr<FunctionCloner> function_cloner) {
        for (size_t i = 0; i < operands.size(); ++i) {
            auto ir_old = operands[i];

            if (is<Function>(ir_old)) {
                if (not function_cloner->value_dict[ir_old]) {
                    ir_old->clone(function_cloner);
                }
            }

            operands[i] = nullptr;  // 置零以避免干扰原来的操作数
            auto ir_new = function_cloner->value_dict[ir_old];
            PRAJNA_ASSERT(ir_new);
            operand(ir_new, i);
        }
    }

   protected:
    std::vector<std::shared_ptr<Value>> operands;
};

class ThisWrapper : virtual public VariableLiked, virtual public Instruction {
   protected:
    ThisWrapper() = default;

   public:
    static std::shared_ptr<ThisWrapper> create(std::shared_ptr<Value> ir_this_pointer) {
        std::shared_ptr<ThisWrapper> self(new ThisWrapper);
        self->operandResize(1);
        self->thisPointer(ir_this_pointer);
        auto ir_pointer_type = cast<PointerType>(ir_this_pointer->type);
        PRAJNA_ASSERT(ir_pointer_type);
        self->type = ir_pointer_type->value_type;
        self->tag = "ThisWrapper";
        return self;
    }

    std::shared_ptr<Value> thisPointer() { return this->operand(0); }
    void thisPointer(std::shared_ptr<Value> ir_this) { this->operand(ir_this, 0); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<ThisWrapper> ir_new(new ThisWrapper(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

/// @brief 用于访问结构体的字段, 最终会变为指针偏移的方式, Constant在lowering的时候就做单独处理
class AccessField : virtual public VariableLiked, virtual public Instruction {
   protected:
    AccessField() = default;

   public:
    static std::shared_ptr<AccessField> create(std::shared_ptr<Value> ir_object,
                                               std::shared_ptr<Field> field) {
        PRAJNA_ASSERT(is<VariableLiked>(ir_object));

        std::shared_ptr<AccessField> self(new AccessField);
        self->operandResize(1);
        self->object(ir_object);
        self->field = field;
        self->type = field->type;
        self->tag = "FieldAccess";
        return self;
    }

    std::shared_ptr<Value> object() { return this->operand(0); }
    void object(std::shared_ptr<Value> ir_object) { this->operand(ir_object, 0); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<AccessField> ir_new(new AccessField(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }

   public:
    std::shared_ptr<Field> field;
};

class IndexArray : virtual public VariableLiked, virtual public Instruction {
   protected:
    IndexArray() = default;

   public:
    static std::shared_ptr<IndexArray> create(std::shared_ptr<Value> ir_object,
                                              std::shared_ptr<Value> ir_index) {
        PRAJNA_ASSERT(is<VariableLiked>(ir_object));

        std::shared_ptr<IndexArray> self(new IndexArray);
        self->operandResize(2);
        self->object(ir_object);
        self->index(ir_index);
        auto ir_array_type = cast<ArrayType>(ir_object->type);
        PRAJNA_ASSERT(ir_array_type);
        self->type = ir_array_type->value_type;
        self->tag = "IndexArray";
        return self;
    }

    std::shared_ptr<Value> object() { return this->operand(0); }
    void object(std::shared_ptr<Value> ir_object) { this->operand(ir_object, 0); }

    std::shared_ptr<Value> index() { return this->operand(1); }
    void index(std::shared_ptr<Value> ir_index) { this->operand(ir_index, 1); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<IndexArray> ir_new(new IndexArray(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class IndexPointer : virtual public VariableLiked, virtual public Instruction {
   protected:
    IndexPointer() = default;

   public:
    static std::shared_ptr<IndexPointer> create(std::shared_ptr<Value> ir_object,
                                                std::shared_ptr<Value> ir_index) {
        PRAJNA_ASSERT(is<VariableLiked>(ir_object));

        std::shared_ptr<IndexPointer> self(new IndexPointer);
        self->operandResize(2);
        self->object(ir_object);
        self->index(ir_index);
        auto ir_pointer_type = cast<PointerType>(ir_object->type);
        PRAJNA_ASSERT(ir_pointer_type);
        self->type = ir_pointer_type->value_type;
        self->tag = "IndexPointer";
        return self;
    }

    std::shared_ptr<Value> object() { return this->operand(0); }
    void object(std::shared_ptr<Value> ir_object) { this->operand(ir_object, 0); }

    std::shared_ptr<Value> index() { return this->operand(1); }
    void index(std::shared_ptr<Value> ir_index) { this->operand(ir_index, 1); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<IndexPointer> ir_new(new IndexPointer(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class GetStructElementPointer : public Instruction {
   protected:
    GetStructElementPointer() = default;

   public:
    /// @param ir_pointer 起始指针
    /// @param index 指针偏移下标, 对于结构体来说相当于字段的号数
    static std::shared_ptr<GetStructElementPointer> create(std::shared_ptr<Value> ir_pointer,
                                                           std::shared_ptr<Field> ir_field) {
        std::shared_ptr<GetStructElementPointer> self(new GetStructElementPointer);
        self->operandResize(1);
        self->pointer(ir_pointer);
        self->field = ir_field;
        self->type = PointerType::create(ir_field->type);
        self->tag = "GetStructElementPointer";
        return self;
    }

    std::shared_ptr<Value> pointer() { return this->operand(0); }
    void pointer(std::shared_ptr<Value> ir_pointer) { this->operand(ir_pointer, 0); }

    /// @brief  指针偏移下标, 对于结构体来说相当于字段的号数
    std::shared_ptr<Field> field;

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<GetStructElementPointer> ir_new(new GetStructElementPointer(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

/// @brief 和llvm::GetElementPtrInst相对应,参数也一致这样更好生成代码,
/// 某种意义上该类的接口有点不太合理
/// @return
class GetArrayElementPointer : public Instruction {
   protected:
    GetArrayElementPointer() = default;

   public:
    /// @param ir_pointer 起始指针
    /// @param index 指针偏移下标, 对于结构体来说相当于字段的号数
    static std::shared_ptr<GetArrayElementPointer> create(std::shared_ptr<Value> ir_pointer,
                                                          std::shared_ptr<Value> ir_index) {
        std::shared_ptr<GetArrayElementPointer> self(new GetArrayElementPointer);
        self->operandResize(2);
        self->pointer(ir_pointer);
        self->index(ir_index);
        auto ir_pointer_type = cast<PointerType>(ir_pointer->type);
        PRAJNA_ASSERT(ir_pointer_type);
        auto ir_array_type = cast<ArrayType>(ir_pointer_type->value_type);
        PRAJNA_ASSERT(ir_array_type);
        self->type = PointerType::create(ir_array_type->value_type);
        self->tag = "GetArrayElementPointer";
        return self;
    }

    std::shared_ptr<Value> pointer() { return this->operand(0); }
    void pointer(std::shared_ptr<Value> ir_pointer) { this->operand(ir_pointer, 0); }

    std::shared_ptr<Value> index() { return this->operand(1); }
    void index(std::shared_ptr<Value> ir_index) { this->operand(ir_index, 1); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<GetArrayElementPointer> ir_new(new GetArrayElementPointer(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class GetPointerElementPointer : public Instruction {
   protected:
    GetPointerElementPointer() = default;

   public:
    /// @param ir_pointer 起始指针
    /// @param index 指针偏移下标, 对于结构体来说相当于字段的号数
    static std::shared_ptr<GetPointerElementPointer> create(std::shared_ptr<Value> ir_pointer,
                                                            std::shared_ptr<Value> ir_index) {
        std::shared_ptr<GetPointerElementPointer> self(new GetPointerElementPointer);
        self->operandResize(2);
        self->pointer(ir_pointer);
        self->index(ir_index);
        auto ir_pointer_type = cast<PointerType>(ir_pointer->type);
        PRAJNA_ASSERT(ir_pointer_type);
        self->type = ir_pointer_type->value_type;
        PRAJNA_ASSERT(is<PointerType>(self->type));
        self->tag = "GetPointerElementPointer";
        return self;
    }

    std::shared_ptr<Value> pointer() { return this->operand(0); }
    void pointer(std::shared_ptr<Value> ir_pointer) { this->operand(ir_pointer, 0); }

    std::shared_ptr<Value> index() { return this->operand(1); }
    void index(std::shared_ptr<Value> ir_index) { this->operand(ir_index, 1); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<GetPointerElementPointer> ir_new(new GetPointerElementPointer(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class DeferencePointer : virtual public VariableLiked, virtual public Instruction {
   protected:
    DeferencePointer() = default;

   public:
    static std::shared_ptr<DeferencePointer> create(std::shared_ptr<Value> ir_pointer) {
        PRAJNA_ASSERT(ir_pointer);
        std::shared_ptr<DeferencePointer> self(new DeferencePointer);
        self->operandResize(1);
        self->pointer(ir_pointer);
        auto ir_pointer_type = cast<PointerType>(ir_pointer->type);
        PRAJNA_ASSERT(ir_pointer_type);
        self->type = ir_pointer_type->value_type;
        self->tag = "DeferencePointer";
        return self;
    }

    std::shared_ptr<Value> pointer() { return this->operand(0); }
    void pointer(std::shared_ptr<Value> ir_pointer) { this->operand(ir_pointer, 0); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<DeferencePointer> ir_new(new DeferencePointer(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class WriteVariableLiked : public Instruction {
   protected:
    WriteVariableLiked() = default;

   public:
    static std::shared_ptr<WriteVariableLiked> create(std::shared_ptr<Value> ir_value,
                                                      std::shared_ptr<VariableLiked> ir_variable) {
        PRAJNA_ASSERT(ir_value);
        PRAJNA_ASSERT(ir_variable);
        PRAJNA_ASSERT(ir_value->type == ir_variable->type);

        // 需要利用std::shared_ptr<Insturction>来初始化enable_shared_from_this的weak_ptr指针
        std::shared_ptr<WriteVariableLiked> self(new WriteVariableLiked);
        self->operandResize(2);
        self->variable(ir_variable);
        self->value(ir_value);
        self->tag = "WriteVariableLiked";
        return self;
    }

    std::shared_ptr<Value> value() { return this->operand(0); }
    void value(std::shared_ptr<Value> ir_value) { return this->operand(ir_value, 0); }

    std::shared_ptr<VariableLiked> variable() { return cast<VariableLiked>(this->operand(1)); }
    void variable(std::shared_ptr<VariableLiked> ir_variable) {
        return this->operand(ir_variable, 1);
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<WriteVariableLiked> ir_new(new WriteVariableLiked(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class GetAddressOfVariableLiked : public Instruction {
   protected:
    GetAddressOfVariableLiked() = default;

   public:
    static std::shared_ptr<GetAddressOfVariableLiked> create(
        std::shared_ptr<VariableLiked> ir_variable_liked) {
        PRAJNA_ASSERT(ir_variable_liked);
        std::shared_ptr<GetAddressOfVariableLiked> self(new GetAddressOfVariableLiked);
        self->operandResize(1);
        self->variable(ir_variable_liked);
        self->type = PointerType::create(ir_variable_liked->type);
        self->tag = "GetAddressOfVariableLiked";
        return self;
    }

    std::shared_ptr<VariableLiked> variable() { return cast<VariableLiked>(this->operand(0)); }
    void variable(std::shared_ptr<VariableLiked> ir_variable_liked) {
        this->operand(ir_variable_liked, 0);
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<GetAddressOfVariableLiked> ir_new(new GetAddressOfVariableLiked(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class Alloca : public Instruction {
   protected:
    Alloca() = default;

   public:
    static std::shared_ptr<Alloca> create(std::shared_ptr<Type> type) {
        auto self =
            cast<Alloca>(std::shared_ptr<Instruction>(static_cast<Instruction*>(new Alloca)));
        self->operandResize(0);
        self->type = PointerType::create(type);
        self->tag = "Alloca";
        return self;
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<Alloca> ir_new(new Alloca(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class GlobalVariable;

/**
 * @note 和llvm::GlobalVariable有一定的对应关系
 */
class GlobalAlloca : public Instruction {
   protected:
    GlobalAlloca() = default;

   public:
    static std::shared_ptr<GlobalAlloca> create(std::shared_ptr<Type> type) {
        std::shared_ptr<GlobalAlloca> self(new GlobalAlloca);
        self->operandResize(0);
        self->type = PointerType::create(type);
        self->tag = "GlobalAlloca";
        return self;
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<GlobalAlloca> ir_new(new GlobalAlloca(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }

   public:
    bool is_external = false;
    sp<Module> parent_module;
    // std::shared_ptr<GlobalVariable> link_to_global_variable = nullptr;
};

class LoadPointer : public Instruction {
   protected:
    LoadPointer() = default;

   public:
    // 讲_type设置为VoidType而不是nullptr,
    // 因为设置为nullptr的话,后续对type()的使用都得先判断是否为nullptr,并不方便
    static std::shared_ptr<LoadPointer> create(std::shared_ptr<Value> pointer) {
        std::shared_ptr<LoadPointer> self(new LoadPointer);
        self->operandResize(1);
        self->pointer(pointer);
        auto ir_pointer_type = cast<PointerType>(pointer->type);
        PRAJNA_ASSERT(ir_pointer_type);
        self->type = ir_pointer_type->value_type;
        self->tag = "LoadPointer";
        return self;
    }

    std::shared_ptr<Value> pointer() { return this->operand(0); }
    void pointer(std::shared_ptr<Value> ir_pointer) { return this->operand(ir_pointer, 0); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<LoadPointer> ir_new(new LoadPointer(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class StorePointer : public Instruction {
   protected:
    StorePointer() = default;

   public:
    static std::shared_ptr<StorePointer> create(std::shared_ptr<Value> value,
                                                std::shared_ptr<Value> pointer) {
        auto ir_pointer_type = cast<PointerType>(pointer->type);
        PRAJNA_ASSERT(ir_pointer_type);
        PRAJNA_ASSERT(ir_pointer_type->value_type == value->type);
        std::shared_ptr<StorePointer> self(new StorePointer);
        self->operandResize(2);
        self->pointer(pointer);
        self->value(value);
        self->tag = "StorePointer";
        return self;
    }

    std::shared_ptr<Value> value() { return this->operand(0); }
    void value(std::shared_ptr<Value> ir_value) { return this->operand(ir_value, 0); }

    std::shared_ptr<Value> pointer() { return this->operand(1); }
    void pointer(std::shared_ptr<Value> ir_pointer) { return this->operand(ir_pointer, 1); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<StorePointer> ir_new(new StorePointer(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class Return : public Instruction {
   protected:
    Return() = default;

   public:
    static std::shared_ptr<Return> create(std::shared_ptr<Value> value) {
        PRAJNA_ASSERT(value);
        auto self =
            cast<Return>(std::shared_ptr<Instruction>(static_cast<Instruction*>(new Return)));
        self->operandResize(1);
        self->type = value->type;
        self->value(value);
        self->tag = "Return";
        return self;
    }

    std::shared_ptr<Value> value() { return this->operand(0); }
    void value(std::shared_ptr<Value> ir_value) { this->operand(ir_value, 0); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<Return> ir_new(new Return(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class BitCast : public Instruction {
   protected:
    BitCast() = default;

   public:
    static std::shared_ptr<BitCast> create(std::shared_ptr<Value> ir_value,
                                           std::shared_ptr<Type> ir_type) {
        auto self =
            cast<BitCast>(std::shared_ptr<Instruction>(static_cast<Instruction*>(new BitCast)));
        self->operandResize(1);
        self->value(ir_value);
        self->type = ir_type;
        self->tag = "BitCast";
        return self;
    };

    std::shared_ptr<Value> value() { return this->operand(0); }
    void value(std::shared_ptr<Value> ir_value) { this->operand(ir_value, 0); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<BitCast> ir_new(new BitCast(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class Call : public Instruction {
   protected:
    Call() = default;

   public:
    static std::shared_ptr<Call> create(std::shared_ptr<Value> ir_value,
                                        std::vector<std::shared_ptr<Value>> arguments) {
        std::shared_ptr<Call> self(new Call);
        self->operandResize(1 + arguments.size());
        self->function(ir_value);
        auto ir_function_type = ir_value->getFunctionType();
        PRAJNA_ASSERT(ir_function_type);
        PRAJNA_ASSERT(ir_function_type->argument_types.size() == arguments.size());
        for (size_t i = 0; i < arguments.size(); ++i) {
            PRAJNA_ASSERT(ir_function_type->argument_types[i] == arguments[i]->type);
            self->argument(i, arguments[i]);
        }

        self->type = ir_function_type->return_type;
        self->tag = "Call";
        return self;
    }

    std::shared_ptr<Value> function() { return this->operand(0); }
    void function(std::shared_ptr<Value> ir_value) { this->operand(ir_value, 0); }

    std::shared_ptr<Value> argument(size_t i) { return this->operand(1 + i); }
    void argument(size_t i, std::shared_ptr<Value> ir_argument) {
        this->operand(ir_argument, i + 1);
    }

    size_t argumentSize() { return this->operandSize() - 1; }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<Call> ir_new(new Call(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class ConditionBranch : public Instruction {
   protected:
    ConditionBranch() = default;

   public:
    static std::shared_ptr<ConditionBranch> create(std::shared_ptr<Value> condition,
                                                   std::shared_ptr<Block> ir_true_block,
                                                   std::shared_ptr<Block> ir_false_block) {
        std::shared_ptr<ConditionBranch> self(new ConditionBranch);
        self->operandResize(3);
        self->condition(condition);
        self->trueBlock(ir_true_block);
        self->falseBlock(ir_false_block);
        self->tag = "ConditionBranch";
        return self;
    }

    std::shared_ptr<Value> condition() { return this->operand(0); }
    void condition(std::shared_ptr<Value> ir_condition) { this->operand(ir_condition, 0); }

    std::shared_ptr<Block> trueBlock() { return cast<Block>(this->operand(1)); }
    void trueBlock(std::shared_ptr<Block> ir_true_block) { this->operand(ir_true_block, 1); }

    std::shared_ptr<Block> falseBlock() { return cast<Block>(this->operand(2)); }
    void falseBlock(std::shared_ptr<Block> ir_false_block) { this->operand(ir_false_block, 2); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<ConditionBranch> ir_new(new ConditionBranch(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class JumpBranch : public Instruction {
   protected:
    JumpBranch() = default;

   public:
    static std::shared_ptr<JumpBranch> create(std::shared_ptr<Block> ir_next) {
        std::shared_ptr<JumpBranch> self(new JumpBranch);
        self->operandResize(1);
        self->nextBlock(ir_next);
        self->tag = "JumpBranch";
        return self;
    }

    std::shared_ptr<Block> nextBlock() { return cast<Block>(this->operand(0)); }
    void nextBlock(std::shared_ptr<Block> ir_next) { this->operand(ir_next, 0); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<JumpBranch> ir_new(new JumpBranch(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

/// @brief 仅仅用于辅助IR的转换, 在最终的IR里不应当出现
class Label : public Block {
   protected:
    Label() = default;

   public:
    static std::shared_ptr<Label> create() {
        std::shared_ptr<Label> self(new Label);
        self->tag = "Label";
        return self;
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<Label> ir_new(new Label(*this));
        return ir_new;
    }
};

/// @brief 用于返回函数参数, 由多个Value构成的
class ValueCollection : public Value, public std::vector<std::shared_ptr<Value>> {};

class If : public Instruction {
   protected:
    If() = default;

   public:
    static std::shared_ptr<If> create(std::shared_ptr<Value> ir_condition,
                                      std::shared_ptr<Block> ir_true_block,
                                      std::shared_ptr<Block> ir_false_block) {
        std::shared_ptr<If> self(new If);
        self->operandResize(3);
        self->condition(ir_condition);
        self->trueBlock(ir_true_block);
        self->falseBlock(ir_false_block);
        self->tag = "If";
        return self;
    }

    std::shared_ptr<Value> condition() { return this->operand(0); }
    void condition(std::shared_ptr<Value> ir_condition) { this->operand(ir_condition, 0); }

    std::shared_ptr<Block> trueBlock() { return cast<Block>(this->operand(1)); }
    void trueBlock(std::shared_ptr<Block> ir_true_block) { this->operand(ir_true_block, 1); }

    std::shared_ptr<Block> falseBlock() { return cast<Block>(this->operand(2)); }
    void falseBlock(std::shared_ptr<Block> ir_false_block) { this->operand(ir_false_block, 2); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<If> ir_new(new If(*this));
        function_cloner->value_dict[trueBlock()] = trueBlock()->clone(function_cloner);
        function_cloner->value_dict[falseBlock()] = falseBlock()->clone(function_cloner);
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class While : public Instruction {
   protected:
    While() = default;

   public:
    static std::shared_ptr<While> create(std::shared_ptr<Value> ir_condition,
                                         std::shared_ptr<Block> ir_condition_block,
                                         std::shared_ptr<Block> ir_true_block) {
        std::shared_ptr<While> self(new While);
        self->operandResize(3);
        self->condition(ir_condition);
        self->conditionBlock(ir_condition_block);
        self->trueBlock(ir_true_block);
        self->tag = "While";
        return self;
    }

    std::shared_ptr<Value> condition() { return this->operand(0); }
    void condition(std::shared_ptr<Value> ir_condition) { this->operand(ir_condition, 0); }

    std::shared_ptr<Block> conditionBlock() { return cast<Block>(this->operand(1)); }
    void conditionBlock(std::shared_ptr<Block> ir_condition_block) {
        this->operand(ir_condition_block, 1);
    }

    std::shared_ptr<Block> loopBlock() { return cast<Block>(this->operand(2)); }
    void trueBlock(std::shared_ptr<Block> ir_true_block) { this->operand(ir_true_block, 2); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<While> ir_new(new While(*this));
        function_cloner->value_dict[conditionBlock()] = conditionBlock()->clone(function_cloner);
        function_cloner->value_dict[loopBlock()] = loopBlock()->clone(function_cloner);
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class For : public Instruction {
   protected:
    For() = default;

   public:
    static std::shared_ptr<For> create(std::shared_ptr<LocalVariable> ir_index,
                                       std::shared_ptr<Value> ir_first,
                                       std::shared_ptr<Value> ir_last,
                                       std::shared_ptr<Block> ir_loop_block) {
        // std::shared_ptr<For> self(new For);
        std::shared_ptr<For> self(new For);
        self->operandResize(4);
        self->index(ir_index);
        self->first(ir_first);
        self->last(ir_last);
        self->loopBlock(ir_loop_block);
        self->tag = "For";
        return self;
    }

    std::shared_ptr<LocalVariable> index() { return cast<LocalVariable>(this->operand(0)); }
    void index(std::shared_ptr<LocalVariable> ir_index) { this->operand(ir_index, 0); }

    std::shared_ptr<Value> first() { return this->operand(1); }
    void first(std::shared_ptr<Value> ir_first) { this->operand(ir_first, 1); }

    std::shared_ptr<Value> last() { return this->operand(2); }
    void last(std::shared_ptr<Value> ir_last) { this->operand(ir_last, 2); }

    std::shared_ptr<Block> loopBlock() { return cast<Block>(this->operand(3)); }
    void loopBlock(std::shared_ptr<Block> ir_loop_block) { this->operand(ir_loop_block, 3); }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<For> ir_new(new For(*this));
        function_cloner->value_dict[index()] = index()->clone(function_cloner);
        function_cloner->value_dict[loopBlock()] = loopBlock()->clone(function_cloner);
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

/**
 * @note 和llvm::GlobalVariable有本质的不同, llvm::GlobalVariable本质是个地址(指针)
 */
class GlobalVariable : public Variable {
   protected:
    GlobalVariable() = default;

   public:
    static std::shared_ptr<GlobalVariable> create(std::shared_ptr<Type> ir_type) {
        std::shared_ptr<GlobalVariable> self(new GlobalVariable);
        self->type = ir_type;
        self->tag = "GlobalVariable";
        return self;
    }

   public:
    bool is_external = false;

    std::shared_ptr<Module> parent_module = nullptr;
};

class AccessProperty : public WriteReadAble, virtual public Instruction {
   protected:
    AccessProperty() = default;

   public:
    static std::shared_ptr<AccessProperty> create(std::shared_ptr<Value> ir_this_pointer,
                                                  std::shared_ptr<ir::Property> ir_property) {
        std::shared_ptr<AccessProperty> self(new AccessProperty);
        PRAJNA_ASSERT(ir_property->getter_function);
        self->type = ir_property->getter_function->function_type->return_type;
        self->operandResize(1);
        self->thisPointer(ir_this_pointer);
        self->property = ir_property;
        self->tag = "AccessProperty";

        if (not ir_property->setter_function) {
            self->is_writeable = false;
        }

        return self;
    }

    std::shared_ptr<Value> thisPointer() { return this->operand(0); }
    void thisPointer(std::shared_ptr<Value> ir_this_pointer) { this->operand(ir_this_pointer, 0); }

    void arguments(std::vector<std::shared_ptr<Value>> ir_arguments) {
        this->operandResize(1 + ir_arguments.size());
        for (size_t i = 0; i < ir_arguments.size(); ++i) {
            this->operand(ir_arguments[i], i + 1);
        }
    }

    std::vector<std::shared_ptr<Value>> arguments() {
        std::vector<std::shared_ptr<Value>> ir_arguments(this->operandSize() - 1);
        for (size_t i = 0; i < ir_arguments.size(); ++i) {
            ir_arguments[i] = this->operand(1 + i);
        }

        return ir_arguments;
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<AccessProperty> ir_new(new AccessProperty(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }

   public:
    std::shared_ptr<ir::Property> property;
};

class WriteProperty : public Instruction {
   protected:
    WriteProperty() = default;

   public:
    static std::shared_ptr<WriteProperty> create(
        std::shared_ptr<Value> ir_value, std::shared_ptr<AccessProperty> ir_access_property) {
        PRAJNA_ASSERT(ir_value);
        PRAJNA_ASSERT(ir_access_property);
        PRAJNA_ASSERT(ir_value->type == ir_access_property->type);

        // 需要利用std::shared_ptr<Insturction>来初始化enable_shared_from_this的weak_ptr指针
        std::shared_ptr<WriteProperty> self(new WriteProperty);
        self->operandResize(2);
        self->property(ir_access_property);
        self->value(ir_value);
        self->tag = "WriteProperty";
        return self;
    }

    std::shared_ptr<Value> value() { return this->operand(0); }
    void value(std::shared_ptr<Value> ir_value) { return this->operand(ir_value, 0); }

    std::shared_ptr<AccessProperty> property() { return cast<AccessProperty>(this->operand(1)); }
    void property(std::shared_ptr<AccessProperty> ir_access_property) {
        return this->operand(ir_access_property, 1);
    }

    std::shared_ptr<Value> clone(std::shared_ptr<FunctionCloner> function_cloner) override {
        std::shared_ptr<WriteProperty> ir_new(new WriteProperty(*this));
        ir_new->cloneOperands(function_cloner);
        return ir_new;
    }
};

class Module : public Named, public std::enable_shared_from_this<Module> {
   protected:
    Module() = default;

   public:
    static std::shared_ptr<Module> create() {
        auto self = std::shared_ptr<Module>(new Module);
        // @todo 后面需要进一步处理
        self->modules[ir::Target::nvptx] = std::shared_ptr<Module>(new Module);

        return self;
    }

    // bool empty()

    std::list<std::shared_ptr<Function>> functions;
    std::list<std::shared_ptr<GlobalVariable>> global_variables;
    std::list<std::shared_ptr<GlobalAlloca>> global_allocas;

    std::shared_ptr<lowering::SymbolTable> symbol_table = nullptr;

    std::shared_ptr<Module> parent_module = nullptr;

    std::map<Target, std::shared_ptr<Module>> modules;

    llvm::Module* llvm_module = nullptr;
};

#pragma region("nvptx")

class KernelFunctionCall : public Instruction {
   protected:
    KernelFunctionCall() = default;

   public:
    static std::shared_ptr<KernelFunctionCall> create(
        std::shared_ptr<Value> ir_function_value, std::shared_ptr<Value> ir_grid_dim,
        std::shared_ptr<Value> ir_block_dim, std::vector<std::shared_ptr<Value>> arguments) {
        std::shared_ptr<KernelFunctionCall> self(new KernelFunctionCall);
        self->operandResize(3 + arguments.size());
        self->function(ir_function_value);
        auto ir_function_type = ir_function_value->getFunctionType();
        PRAJNA_ASSERT(ir_function_type);
        PRAJNA_ASSERT(ir_function_type->annotations.count("kernel"));
        self->gridDim(ir_grid_dim);
        self->blockDim(ir_block_dim);
        for (size_t i = 0; i < arguments.size(); ++i) {
            PRAJNA_ASSERT(ir_function_type->argument_types[i] == arguments[i]->type);
            self->argument(i, arguments[i]);
        }

        self->type = ir_function_type->return_type;
        self->tag = "KernelFunctionCall";
        return self;
    }

    std::shared_ptr<Value> function() { return this->operand(0); }
    void function(std::shared_ptr<Value> ir_value) { this->operand(ir_value, 0); }

    std::shared_ptr<Value> gridDim() { return this->operand(1); }
    void gridDim(std::shared_ptr<Value> ir_grid_dim) { this->operand(ir_grid_dim, 1); }

    std::shared_ptr<Value> blockDim() { return this->operand(2); }
    void blockDim(std::shared_ptr<Value> ir_block_dim) { this->operand(ir_block_dim, 2); }

    size_t argumentSize() { return this->operandSize() - 3; }

    std::shared_ptr<Value> argument(size_t i) { return this->operand(3 + i); }
    void argument(size_t i, std::shared_ptr<Value> ir_argument) {
        this->operand(ir_argument, i + 3);
    }

    std::vector<std::shared_ptr<Value>> arguments() {
        std::vector<std::shared_ptr<Value>> arguments_re;
        for (size_t i = 0; i < this->operandSize(); ++i) {
            arguments_re.push_back(this->argument(i));
        }

        return arguments_re;
    }
};

#pragma endregion("nvptx")

inline std::shared_ptr<Function> Value::getParentFunction() {
    PRAJNA_ASSERT(parent_block);
    return parent_block->getParentFunction();
}

inline std::shared_ptr<Block> Value::getRootBlock() {
    PRAJNA_ASSERT(this->parent_block);
    auto root = this->parent_block;
    while (root->parent_block) {
        root = root->parent_block;
    }

    return root;
}

}  // namespace prajna::ir
