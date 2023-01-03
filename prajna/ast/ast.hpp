#pragma once

#include <list>
#include <optional>
#include <vector>

#include "boost/fusion/include/adapt_struct.hpp"
#include "boost/fusion/include/io.hpp"
#include "boost/optional.hpp"
// #include "boost/tuple/tuple.hpp" // 感觉匹配属性的时候存在很多问题, 不推荐使用了
#include "boost/variant/recursive_variant.hpp"
#include "prajna/config.hpp"

namespace prajna::ast {

struct SourcePosition {
    int line = -1;
    int column = -1;
    std::string file;
};

struct SourceLocation {
    SourcePosition first_position;
    SourcePosition last_position;
};

struct Blank : SourceLocation {};

struct Unary;
struct PostfixUnary;
struct Expression;
struct Expressions;
struct Cast;
struct KernelFunctionCall;
struct PrefixCall;
struct Array;
/// @note  operator const char*() const 函数在boost::spirit的debug node的模式下是需要的,
/// 但用处不大故直接删除了

struct Null : SourceLocation {};

struct Operator : SourceLocation {
    Operator() = default;

    explicit Operator(const std::string& chars_) : string_token(chars_) {}

    std::string string_token;
};

inline bool operator==(const Operator& lhs, const Operator& rhs) {
    return (lhs.string_token == rhs.string_token);
}

inline bool operator!=(const Operator& lhs, const Operator& rhs) {
    return !(lhs.string_token == rhs.string_token);
}

struct Identifier : public std::string, public SourceLocation {
    Identifier() : std::string() {}
    Identifier(const Identifier& rhs) : std::string(rhs) {
        first_position = rhs.first_position;
        last_position = rhs.last_position;
    }

    explicit Identifier(const std::string& s) : std::string(s) {}

    Identifier& operator=(const Identifier& other) {
        std::string::operator=(other);
        first_position = other.first_position;
        last_position = other.last_position;
        return *this;
    }

    Identifier& operator=(const std::string& other) {
        std::string::operator=(other);
        return *this;
    }
};

struct BoolLiteral : SourceLocation {
    bool value;
};

struct IntLiteral : SourceLocation {
    int64_t value;

    // TODO 后期再做处理, 我们先不处理
    // boost::multiprecision::cpp_int mp_int_value;
};

struct IntLiteralPostfix : SourceLocation {
    IntLiteral int_literal;
    Identifier postfix;
};

struct FloatLiteral : SourceLocation {
    double value;
};

struct FloatLiteralPostfix : SourceLocation {
    FloatLiteral float_literal;
    Identifier postfix;
};

struct CharLiteral : SourceLocation {
    char value;
};

struct StringLiteral : SourceLocation {
    std::string value;
};

struct Type;
struct IdentifiersResolution;

using TemplateArgument = boost::variant<Blank, boost::recursive_wrapper<Type>, IntLiteral>;
// using TemplateArguments = std::list<TemplateArgument>;

struct TemplateArguments : SourceLocation, std::list<TemplateArgument> {};

struct IdentifierWithTemplateArguments : SourceLocation {
    Identifier identifier;
    // @note boost::optional是不可以省略的, 会有未知错误,
    // 可能和boost::recursive_wrapper混合使用有关, 目前就不省略了
    boost::optional<TemplateArguments> template_arguments;
};

struct IdentifiersResolution : SourceLocation {
    boost::optional<Operator> is_root;
    std::vector<IdentifierWithTemplateArguments> identifiers;
};

struct Import : SourceLocation {
    IdentifiersResolution identifier_path;
    boost::optional<Identifier> as;
};

struct Export : SourceLocation {
    Identifier identifier;
};

using PostfixTypeOperator = boost::variant<Operator, IntLiteral, Identifier>;

struct Type : SourceLocation {
    IdentifiersResolution base_type;
    std::vector<PostfixTypeOperator> postfix_type_operators;
};

using PostfixType = Type;

struct SizeOf : SourceLocation {
    Type type;
};

typedef boost::variant<
    Blank, Null, CharLiteral, StringLiteral, BoolLiteral, IntLiteral, FloatLiteral, Identifier,
    IdentifiersResolution, IntLiteralPostfix, FloatLiteralPostfix, boost::recursive_wrapper<Unary>,
    boost::recursive_wrapper<PostfixUnary>, boost::recursive_wrapper<Expression>,
    boost::recursive_wrapper<Expressions>, boost::recursive_wrapper<Cast>,
    boost::recursive_wrapper<Array>, SizeOf, boost::recursive_wrapper<KernelFunctionCall>>
    Operand;

struct Unary : SourceLocation {
    Operator operator_;
    Operand operand;
};

struct PostfixUnary : SourceLocation {
    Operand operand;
    std::vector<Operator> operators;
};

struct BinaryOperation : SourceLocation {
    Operator operator_;
    Operand operand;
};

struct Expression : SourceLocation {
    Operand first;
    std::vector<BinaryOperation> rest;
};

struct Cast : SourceLocation {
    Type type;
    Expression value;
};

struct Expressions : SourceLocation, std::vector<Expression> {};

struct Array : SourceLocation {
    std::vector<Expression> values;
};

struct VariableDeclaration : SourceLocation {
    Identifier name;
    boost::optional<Type> type;
    boost::optional<Expression> initialize;
};

struct Assignment : SourceLocation {
    Expression left;
    Expression right;
};

struct Break : SourceLocation {};

struct Continue : SourceLocation {};

struct If;
struct While;
struct For;
struct Return;
struct Struct;
struct Interface;
struct ImplementStructForInterface;
struct ImplementStruct;
struct Class;
struct FunctionHeader;
struct Function;
struct Operator;
struct Namespace;
struct Block;

struct require_statement : SourceLocation {
    StringLiteral path;
};

struct using_statement : SourceLocation {
    Operand object;
};

struct Pragma : SourceLocation {
    Identifier name;
    std::vector<StringLiteral> values;
};

struct Annotation : SourceLocation {
    Identifier name;
    std::vector<StringLiteral> values;
};

struct Annotations : SourceLocation, std::list<Annotation> {};

template <typename _T>
struct Annotated {
    Annotations annoations;
    _T statement;
};

typedef boost::variant<
    Blank, boost::recursive_wrapper<Block>, Import, Export, VariableDeclaration, Assignment,
    Expression, boost::recursive_wrapper<If>, boost::recursive_wrapper<While>,
    boost::recursive_wrapper<For>, Break, Continue, boost::recursive_wrapper<Function>,
    boost::recursive_wrapper<Return>, boost::recursive_wrapper<Struct>,
    boost::recursive_wrapper<Interface>, boost::recursive_wrapper<ImplementStructForInterface>,
    boost::recursive_wrapper<ImplementStruct>, Pragma>
    Statement;

// @note需要声明为class, 因为之前才能在其他模块使用前置声明.
struct Statements : SourceLocation, public std::list<Statement> {};

struct Block : SourceLocation {
    Statements statements;
};

struct If : SourceLocation {
    Expression condition;
    Block then;
    boost::optional<Block> else_;
};

struct While : SourceLocation {
    Expression condition;
    Block body;
};

struct For : SourceLocation {
    Annotations annotations;
    Identifier index;
    Expression first;
    Expression last;
    Block body;
};

struct Return : SourceLocation {
    boost::optional<Expression> expr;
};

struct Parameter : SourceLocation {
    Identifier name;
    Type type;
};

struct Parameters : SourceLocation, std::vector<Parameter> {};

struct FunctionHeader : SourceLocation {
    Annotations annotations;
    Identifier name;
    Parameters parameters;
    boost::optional<Type> return_type;
};

struct Function : SourceLocation {
    FunctionHeader declaration;
    boost::optional<Block> body;
};

struct Field : SourceLocation {
    Identifier name;
    Type type;
};

using TemplateParameter = Identifier;
struct TemplateParameters : SourceLocation, std::list<TemplateParameter> {};

struct Struct : SourceLocation {
    Annotations annotations;
    Identifier name;
    TemplateParameters template_parameters;
    std::vector<Field> fields;
};

struct Interface : SourceLocation {
    Identifier name;
    // 函数声明也采用Function, 但其没有实现
    std::vector<Function> function_declarations;
};

struct ImplementStructForInterface : SourceLocation {
    Type struct_;
    Type interface;
    std::vector<Function> functions;
};

struct ImplementStruct : SourceLocation {
    IdentifiersResolution struct_;
    TemplateParameters template_paramters;
    std::vector<Function> functions;
};

struct KernelFunctionCallOperation {
    Expression grid_shape;
    Expression block_shape;
    Expressions arguments;
};

struct KernelFunctionCall : SourceLocation {
    Expression kernel_function;
    boost::optional<KernelFunctionCallOperation> operation;
};

}  // namespace prajna::ast

BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Block, statements)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Cast, type, value)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Unary, operator_, operand)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::PostfixUnary, operand, operators)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::BinaryOperation, operator_, operand)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Assignment, left, right)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Expression, first, rest)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::VariableDeclaration, name, type, initialize)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::If, condition, then, else_)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::While, condition, body)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::For, annotations, index, first, last, body)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Return, expr)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Field, name, type)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::IdentifierWithTemplateArguments, identifier,
                          template_arguments)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Struct, annotations, name, template_parameters, fields)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Parameter, name, type)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::FunctionHeader, annotations, name, parameters, return_type)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Pragma, name, values)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Annotation, name, values)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Function, declaration, body)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Interface, name, function_declarations)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::ImplementStructForInterface, interface, struct_, functions)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::ImplementStruct, struct_, template_paramters, functions)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::IdentifiersResolution, is_root, identifiers)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::PostfixType, base_type, postfix_type_operators)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Import, identifier_path, as)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Export, identifier)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::SizeOf, type)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::IntLiteralPostfix, int_literal, postfix)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::FloatLiteralPostfix, float_literal, postfix)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::KernelFunctionCallOperation, grid_shape, block_shape,
                          arguments)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::KernelFunctionCall, kernel_function, operation)
BOOST_FUSION_ADAPT_STRUCT(prajna::ast::Array, values)
BOOST_FUSION_ADAPT_TPL_STRUCT((_T), (prajna::ast::Annotated)(_T), annotations, statement)
