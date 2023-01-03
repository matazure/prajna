add_library(prajna_jit
    execution_engine.cpp
)

target_link_libraries(prajna_jit
    PUBLIC prajna_config_target
    PRIVATE llvm_include_dir
    PRIVATE LLVMExecutionEngine
    PRIVATE LLVMIRReader
    PRIVATE LLVMJITLink
    PUBLIC LLVMOrcJIT
    PRIVATE LLVMMCJIT
    PRIVATE LLVMX86CodeGen
    PRIVATE LLVMX86AsmParser
    PRIVATE LLVMCodeGen
    PRIVATE LLVMAnalysis
    PRIVATE LLVMTarget
    PRIVATE LLVMSupport
    PRIVATE LLVMX86Desc
    PRIVATE LLVMX86Info
    PRIVATE LLVMAArch64Info
    PRIVATE LLVMAArch64CodeGen
    PRIVATE LLVMAArch64AsmParser
    PRIVATE LLVMAArch64Desc
    PRIVATE LLVMCore
)

target_include_directories(prajna_jit PRIVATE /usr/local/cuda/include)

if (PRAJNA_WITH_GPU)
    target_link_libraries(prajna_jit  PRIVATE /usr/local/cuda/lib64/libcudart.so PRIVATE /usr/local/cuda/lib64/stubs/libcuda.so)
endif()
