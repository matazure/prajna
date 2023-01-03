add_library(prajna_codegen
    llvm_codegen.cpp
)

target_link_libraries(prajna_codegen
    PUBLIC prajna_ir
    PRIVATE llvm_include_dir
    PRIVATE LLVMExecutionEngine
    PRIVATE LLVMCodeGen
    PRIVATE LLVMAnalysis
    PRIVATE LLVMTarget
    PUBLIC LLVMSupport # 外部会用到, 后面有时间在处理, 应该需要-DLLVM_ENABLE_ABI_BREAKING_CHECKS=OFF才可以关闭
    PRIVATE LLVMX86Desc
    PRIVATE LLVMX86Info
    PRIVATE LLVMX86CodeGen
    PRIVATE LLVMX86AsmParser
    PRIVATE LLVMAArch64Desc # 不同平台不同
    PRIVATE LLVMAArch64Info
    PRIVATE LLVMAArch64CodeGen
    PRIVATE LLVMAArch64AsmParser
    PUBLIC LLVMCore # Module在头文件暴露了
)


if (PRAJNA_ENABLE_LLVM_DUMP)
    target_compile_definitions(prajna_codegen PRIVATE PRAJNA_ENABLE_LLVM_DUMP=1)
endif()
if (PRAJNA_ENABLE_LLVM_VERIFY)
    target_compile_definitions(prajna_codegen PRIVATE PRAJNA_ENABLE_LLVM_VERIFY=1)
endif()
