include(cmake/openssl.cmake)

set(CMAKE_SYSTEM_PROGRAM_PATH /opt/homebrew/Cellar/llvm/15.0.4/bin/)

set(JSON_Install ON)
set(CPPZMQ_BUILD_TESTS OFF)
# set(XEUS_ZMQ_BUILD_SHARED_LIBS OFF)
set(XEUS_ZMQ_STATIC_DEPENDENCIES ON)
# set(XEUS_BUILD_SHARED_LIBS OFF)
set(XEUS_STATIC_DEPENDENCIES ON)
set(WITH_LIBSODIUM OFF)
set(OPENSSL_INCLUDE_DIR /home/zhimin/miniconda3/envs/xwidgets/include)
set(OPENSSL_CRYPTO_LIBRARY /home/zhimin/miniconda3/envs/xwidgets/lib/libcrypto.a)
add_subdirectory(third_party/json EXCLUDE_FROM_ALL)
add_subdirectory(third_party/xtl EXCLUDE_FROM_ALL)
add_subdirectory(third_party/xeus EXCLUDE_FROM_ALL)
add_subdirectory(third_party/libzmq EXCLUDE_FROM_ALL)
add_subdirectory(third_party/cppzmq EXCLUDE_FROM_ALL)
add_subdirectory(third_party/xeus-zmq EXCLUDE_FROM_ALL)
add_subdirectory(third_party/xproperty EXCLUDE_FROM_ALL)
add_subdirectory(third_party/xwidgets EXCLUDE_FROM_ALL)

add_executable(xeus_prajna main.cpp)
target_link_libraries(xeus_prajna
    PRIVATE prajna_compiler
    PRIVATE cppzmq-static
    PRIVATE xeus-static
    PRIVATE xeus-zmq-static
    PRIVATE xwidgets-static
    PRIVATE ${CMAKE_DL_LIBS}
)
target_include_directories(xeus_prajna PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_options(xeus_prajna
    PRIVATE -Wno-unused-parameter
    PRIVATE -Wno-deprecated-declarations
)

configure_file (
    share/prajna/kernel.json.in
    ${CMAKE_CURRENT_BINARY_DIR}/share/prajna/kernel.json
)

install(TARGETS xeus_prajna EXPORT ${PROJECT_NAME}-targets)
install(FILES ${CMAKE_CURRENT_BINARY_DIR}/share/prajna/kernel.json
              DESTINATION ${CMAKE_INSTALL_PREFIX}/share/prajna)
