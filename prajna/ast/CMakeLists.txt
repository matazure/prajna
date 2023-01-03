add_library(prajna_ast INTERFACE)
target_link_libraries(prajna_ast
    INTERFACE prajna_config_target
    # PRIVATE Boost::multiprecision
)
