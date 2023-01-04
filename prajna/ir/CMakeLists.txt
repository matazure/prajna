add_library(prajna_ir
    global_context.cpp
)

target_link_libraries(prajna_ir
    PUBLIC prajna_config_target
    PRIVATE llvm_include_dir
)
