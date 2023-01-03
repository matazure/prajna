
#include "prajna/jit/execution_engine.h"

#ifdef PRAJNA_WITH_GPU
#include <cuda.h>
#include <cuda_runtime.h>
#include <nvrtc.h>
#endif

#include <setjmp.h>

#include <algorithm>
#include <atomic>
#include <filesystem>
#include <fstream>
#include <map>

#include "llvm/ExecutionEngine/JITLink/JITLinkMemoryManager.h"
#include "llvm/ExecutionEngine/Orc/LLJIT.h"
#include "llvm/ExecutionEngine/Orc/ObjectLinkingLayer.h"
#include "llvm/ExecutionEngine/SectionMemoryManager.h"
#include "prajna/assert.hpp"
#include "prajna/compiler/compiler.h"
#include "prajna/ir/ir.hpp"
#include "prajna/reference_count.hpp"

namespace prajna {
std::map<void *, std::atomic<int64_t>> ptr_count_dict;
}

namespace prajna::jit {

#ifdef PRAJNA_WITH_GPU
// cudaMalloc是一个重载函数, 故重新包装了一下
cudaError_t cudaMalloc(void **devPtr, size_t size) { return ::cudaMalloc(devPtr, size); }

inline void checkCudaErrors(bool re) { PRAJNA_ASSERT(re == 0); }
#endif

jmp_buf buf;

void c_jmp_exit() { longjmp(buf, 1); }
void c_print(char *c_str) { print_callback(c_str); }
void c_assert(bool t) {
    if (!t) {
        printf("%s\n", "Prajna runtime error");
        longjmp(buf, 1);
    }
}

llvm::ExitOnError exit_on_error;

ExecutionEngine::ExecutionEngine() {
    LLVMInitializeNativeTarget();
    LLVMInitializeNativeAsmPrinter();
    // LLVMInitializeNativeAsmParser();

    auto expect_up_lljit =
        llvm::orc::LLJITBuilder()
            .setObjectLinkingLayerCreator(
                [=](llvm::orc::ExecutionSession &ES, const llvm::Triple &TT) {
                    auto ll = std::make_unique<llvm::orc::ObjectLinkingLayer>(
                        // @note 需要确认机制是做什么用的
                        ES, std::make_unique<llvm::jitlink::InProcessMemoryManager>(64 * 1024));
                    ll->setAutoClaimResponsibilityForObjectSymbols(true);
                    return std::move(ll);
                })
            .create();
    PRAJNA_ASSERT(expect_up_lljit);
    _up_lljit = std::move(*expect_up_lljit);
}

size_t ExecutionEngine::getValue(std::string name) {
    auto expect_symbol = _up_lljit->lookup(name);
    PRAJNA_ASSERT(expect_symbol);
    return expect_symbol->getValue();
}

void ExecutionEngine::addIRModule(std::shared_ptr<ir::Module> ir_module) {
    // host
    auto up_llvm_module = std::unique_ptr<llvm::Module>(ir_module->llvm_module);
    llvm::orc::ThreadSafeModule llvm_orc_thread_module(std::move(up_llvm_module),
                                                       std::make_unique<llvm::LLVMContext>());
    exit_on_error(_up_lljit->addIRModule(std::move(llvm_orc_thread_module)));

    // auto =  ir_module->modules[ir::Tar]

#ifdef PRAJNA_WITH_GPU
    for (auto [ir_target, ir_sub_module] : ir_module->modules) {
        if (not ir_sub_module) continue;

        // @todo 没有核函数,则无需编译, 可优化为没有核函数调用则无需编译, 在transform优化,
        // 先不做处理
        // 这个步骤会消耗显卡内存, 后期优化尽量释放,
        if (std::none_of(RANGE(ir_sub_module->functions),
                         [](std::shared_ptr<ir::Function> ir_function) {
                             return ir_function->function_type->annotations.count("kernel");
                         })) {
            continue;
        }

        // 目前仅支持nvptx后端的gpu
        PRAJNA_ASSERT(ir_target == ir::Target::nvptx);
        auto file_base = (std::filesystem::temp_directory_path() /
                          std::filesystem::path(ir_sub_module->name).stem())
                             .string();
        std::error_code err_code;
        llvm::raw_fd_ostream llvm_fs(file_base + ".ll", err_code);
        ir_sub_module->llvm_module->print(llvm_fs, nullptr);
        llvm_fs.close();
        PRAJNA_VERIFY(
            std::system(("llc " + file_base + ".ll" + " -o " + file_base + ".ptx").c_str()) == 0);

        auto cu_re = cuInit(0);
        PRAJNA_ASSERT(cu_re == CUDA_SUCCESS);
        CUdevice cu_device;
        cu_re = cuDeviceGet(&cu_device, 0);
        PRAJNA_ASSERT(cu_re == CUDA_SUCCESS);
        auto cuda_re = cudaSetDevice(cu_device);
        PRAJNA_ASSERT(cuda_re == cudaSuccess);
        CUcontext cu_context;
        cu_re = cuCtxCreate(&cu_context, 0, cu_device);
        if (cu_re == CUDA_ERROR_OUT_OF_MEMORY) {
            throw std::runtime_error("cuda error out of memory");
        }
        PRAJNA_ASSERT(cu_re == CUDA_SUCCESS);

        const size_t options_size = 6;
        CUjit_option options[options_size];
        void *optionVals[options_size];
        float walltime;
        char error_log[8192], info_log[8192];
        unsigned int logSize = 8192;
        void *cuOut;
        size_t outSize;
        // Setup linker options
        // Return walltime from JIT compilation
        options[0] = CU_JIT_WALL_TIME;
        optionVals[0] = (void *)&walltime;
        // Pass a buffer for info messages
        options[1] = CU_JIT_INFO_LOG_BUFFER;
        optionVals[1] = (void *)info_log;
        // Pass the size of the info buffer
        options[2] = CU_JIT_INFO_LOG_BUFFER_SIZE_BYTES;
        optionVals[2] = (void *)(long)logSize;
        // Pass a buffer for error message
        options[3] = CU_JIT_ERROR_LOG_BUFFER;
        optionVals[3] = (void *)error_log;
        // Pass the size of the error buffer
        options[4] = CU_JIT_ERROR_LOG_BUFFER_SIZE_BYTES;
        optionVals[4] = (void *)(long)logSize;
        // Make the linker verbose
        options[5] = CU_JIT_LOG_VERBOSE;
        optionVals[5] = (void *)1;

        CUmodule cu_module = 0;
        CUfunction cu_kernel_funciton = 0;
        CUlinkState cu_link_state;

        cu_re = cuLinkCreate(options_size, options, optionVals, &cu_link_state);
        PRAJNA_ASSERT(cu_re == CUDA_SUCCESS, std::string(error_log));
        std::fstream fs(file_base + ".ptx");
        std::stringstream ss;
        ss << fs.rdbuf();
        auto ptx_source = ss.str();

        cu_re =
            cuLinkAddData(cu_link_state, CU_JIT_INPUT_PTX, const_cast<char *>(ptx_source.c_str()),
                          strlen(ptx_source.c_str()) + 1, 0, 0, 0, 0);
        PRAJNA_ASSERT(cu_re == CUDA_SUCCESS, std::string(error_log));

        cu_re = cuLinkComplete(cu_link_state, &cuOut, &outSize);
        PRAJNA_ASSERT(cu_re == CUDA_SUCCESS, std::string(error_log));

        // printf("CUDA Link Completed in %fms. Linker Output:\n%s\n", walltime, info_log);
        cu_re = cuModuleLoadData(&cu_module, cuOut);
        PRAJNA_ASSERT(cu_re == CUDA_SUCCESS);

        for (auto ir_function : ir_sub_module->functions) {
            if (ir_function->function_type->annotations.count("kernel")) {
                auto kernel_fun_address_name = getKernelFunctionAddressName(ir_function->fullname);
                auto test_kernel_fun =
                    reinterpret_cast<CUfunction *>(this->getValue(kernel_fun_address_name));
                std::string function_name = mangleNvvmName(ir_function->fullname);
                cu_re = cuModuleGetFunction(test_kernel_fun, cu_module, function_name.c_str());
                PRAJNA_ASSERT(cu_re == CUDA_SUCCESS, std::string(error_log));
            }
        }

        // @todo 一旦释放, 核函数等对象就无效了, 后面需要再进一步优化
        // cuCtxDestroy(cu_context);
    }
#endif
}

void ExecutionEngine::bindCFunction(void *fun_ptr, std::string mangle_name) {
    _up_lljit->getMainJITDylib().addGenerator(
        cantFail(llvm::orc::DynamicLibrarySearchGenerator::GetForCurrentProcess(
            _up_lljit->getDataLayout().getGlobalPrefix())));
    auto fun_symbol = llvm::orc::absoluteSymbols(
        {{_up_lljit->mangleAndIntern(mangle_name),
          {llvm::pointerToJITTargetAddress(fun_ptr),
           llvm::JITSymbolFlags::Exported | llvm::JITSymbolFlags::Absolute}}});
    exit_on_error(_up_lljit->getMainJITDylib().define(fun_symbol));
}

void ExecutionEngine::catchRuntimeError() {
    auto error = setjmp(buf);
    if (error != 0) {
        throw std::runtime_error("Prajna Runtime Error");
    }
}

void ExecutionEngine::bindBuiltinFunction() {
    this->bindCFunction(reinterpret_cast<void *>(c_jmp_exit), "::bindings::jmp_exit_c");
    this->bindCFunction(reinterpret_cast<void *>(c_print), "::bindings::print_c");
    this->bindCFunction(reinterpret_cast<void *>(c_assert), "::bindings::assert");
    this->bindCFunction(reinterpret_cast<void *>(malloc), "::bindings::malloc");
    this->bindCFunction(reinterpret_cast<void *>(free), "::bindings::free");

    this->bindCFunction(reinterpret_cast<void *>(registerReferenceCount),
                        "::bindings::registerReferenceCount");
    this->bindCFunction(reinterpret_cast<void *>(getReferenceCount),
                        "::bindings::getReferenceCount");
    this->bindCFunction(reinterpret_cast<void *>(incReferenceCount),
                        "::bindings::incReferenceCount");
    this->bindCFunction(reinterpret_cast<void *>(decReferenceCount),
                        "::bindings::decReferenceCount");

#ifdef PRAJNA_WITH_GPU
    this->bindCFunction(reinterpret_cast<void *>(cuInit), "::cuda::cuInit");
    this->bindCFunction(reinterpret_cast<void *>(cuDeviceGetCount), "::cuda::cuDeviceGetCount");
    this->bindCFunction(reinterpret_cast<void *>(cuDeviceGetAttribute),
                        "::cuda::cuDeviceGetAttribute");
    this->bindCFunction(reinterpret_cast<void *>(cuLaunchKernel), "::cuda::cuLaunchKernel");
    this->bindCFunction(reinterpret_cast<void *>(cudaSetDevice), "::cuda::cudaSetDevice");
    this->bindCFunction(reinterpret_cast<void *>(::cudaMemcpy), "::cuda::cudaMemcpy");
    // cudaMalloc是一个重载函数, 故重新包装了一下
    this->bindCFunction(reinterpret_cast<void *>(cudaMalloc), "::cuda::cudaMalloc");
    this->bindCFunction(reinterpret_cast<void *>(::cuMemAlloc), "::cuda::cuMemAlloc");
#endif
}

}  // namespace prajna::jit
