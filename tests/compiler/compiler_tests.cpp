

#include <filesystem>
#include <fstream>

#include "gtest/gtest.h"
#include "prajna/compiler/compiler.h"
#include "tests/utility.hpp"

using namespace prajna;

struct PrintFileName {
    template <class ParamType>
    std::string operator()(const testing::TestParamInfo<ParamType>& info) const {
        return std::filesystem::path(info.param).stem();
    }
};

class CompilerSourceTests : public testing::TestWithParam<std::string> {};
TEST_P(CompilerSourceTests, TestSourceFromDirectory) {
    auto compiler = std::make_shared<compiler::Compiler>();
    std::string prajna_source_path = GetParam();
    compiler->compileBuiltinSourceFiles("prajna/builtin_sources");
    compiler->compileFile(".", prajna_source_path);
    compiler->runTestFunctions();
    ASSERT_EQ(0, compiler->compile_error_count);
}

class CompilerScriptTests : public testing::TestWithParam<std::string> {};
TEST_P(CompilerScriptTests, TestScriptFromDirectory) {
    auto compiler = std::make_shared<compiler::Compiler>();
    compiler->compileBuiltinSourceFiles("prajna/builtin_sources");
    std::string prajna_script_path = GetParam();
    std::ifstream ifs(prajna_script_path);
    while (ifs.good()) {
        std::string code;
        std::getline(ifs, code);
        // 修复//注释的问题
        code.append("\n");
        compiler->compileCommandLine(code);
        std::cout << std::endl;
    }
    ASSERT_EQ(0, compiler->compile_error_count);
}

class CompilerErrorSourceTests : public testing::TestWithParam<std::string> {};
TEST_P(CompilerErrorSourceTests, TestSourceFromDirectory) {
    auto compiler = std::make_shared<compiler::Compiler>();
    std::string prajna_source_path = GetParam();
    compiler->compileBuiltinSourceFiles("prajna/builtin_sources");
    compiler->compileFile(".", prajna_source_path);
    compiler->runTestFunctions();
}

class CompilerErrorScriptTests : public testing::TestWithParam<std::string> {};
TEST_P(CompilerErrorScriptTests, TestScriptFromDirectory) {
    auto compiler = std::make_shared<compiler::Compiler>();
    compiler->compileBuiltinSourceFiles("prajna/builtin_sources");
    std::string prajna_script_path = GetParam();
    std::ifstream ifs(prajna_script_path);
    while (ifs.good()) {
        std::string code;
        std::getline(ifs, code);
        // 修复//注释的问题
        code.append("\n");
        compiler->compileCommandLine(code);
        std::cout << std::endl;
    }
}

INSTANTIATE_TEST_SUITE_P(
    CompilerScriptTestsInstance, CompilerScriptTests,
    testing::ValuesIn(prajna::tests::getFiles("tests/compiler/prajna_scripts")), PrintFileName());

// 会遍历整个文件夹里的文件
INSTANTIATE_TEST_SUITE_P(
    CompilerSourceTestsInstance, CompilerSourceTests,
    testing::ValuesIn(prajna::tests::getFiles("tests/compiler/prajna_sources")), PrintFileName());

INSTANTIATE_TEST_SUITE_P(
    CompilerErrorScriptTestsInstance, CompilerErrorScriptTests,
    testing::ValuesIn(prajna::tests::getFiles("tests/compiler/prajna_error_scripts")),
    PrintFileName());

// 会遍历整个文件夹里的文件
INSTANTIATE_TEST_SUITE_P(
    CompilerErrorSourceTestsInstance, CompilerErrorSourceTests,
    testing::ValuesIn(prajna::tests::getFiles("tests/compiler/prajna_error_sources")),
    PrintFileName());

#ifdef PRAJNA_WITH_GPU

INSTANTIATE_TEST_SUITE_P(
    CompilerScriptTestsGpuInstance, CompilerScriptTests,
    testing::ValuesIn(prajna::tests::getFiles("tests/compiler/prajna_gpu_scripts")),
    PrintFileName());

// 会遍历整个文件夹里的文件
INSTANTIATE_TEST_SUITE_P(
    CompilerSourceTestsGpuInstance, CompilerSourceTests,
    testing::ValuesIn(prajna::tests::getFiles("tests/compiler/prajna_gpu_sources")),
    PrintFileName());

INSTANTIATE_TEST_SUITE_P(
    CompilerErrorScriptTestsGpuInstance, CompilerErrorScriptTests,
    testing::ValuesIn(prajna::tests::getFiles("tests/compiler/prajna_error_gpu_scripts")),
    PrintFileName());

// 会遍历整个文件夹里的文件
INSTANTIATE_TEST_SUITE_P(
    CompilerErrorSourceTestsGpuInstance, CompilerErrorSourceTests,
    testing::ValuesIn(prajna::tests::getFiles("tests/compiler/prajna_error_gpu_sources")),
    PrintFileName());

#endif
