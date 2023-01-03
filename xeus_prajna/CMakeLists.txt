include(cmake/openssl.cmake)

set(JSON_Install ON CACHE BOOL "json install target" FORCE)
set(CPPZMQ_BUILD_TESTS OFF CACHE BOOL "disable cppzmp build tests" FORCE)
add_subdirectory(third_party/json EXCLUDE_FROM_ALL)
add_subdirectory(third_party/xtl EXCLUDE_FROM_ALL)
add_subdirectory(third_party/xeus EXCLUDE_FROM_ALL)
add_subdirectory(third_party/libzmq EXCLUDE_FROM_ALL)
add_subdirectory(third_party/cppzmq EXCLUDE_FROM_ALL)
add_subdirectory(third_party/xeus-zmq EXCLUDE_FROM_ALL)

add_executable(xeus_prajna main.cpp)
target_link_libraries(xeus_prajna
    PRIVATE prajna_compiler
    PRIVATE xeus-static
    PRIVATE xeus-zmq-static
)
target_include_directories(xeus_prajna PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_options(xeus_prajna
    PRIVATE -Wno-unused-parameter
    PRIVATE -Wno-deprecated-declarations
)

configure_file (
    share/kernel.json.in
    ${CMAKE_CURRENT_BINARY_DIR}/share/kernel.json
)

install(TARGETS xeus_prajna EXPORT ${PROJECT_NAME}-targets)
install(FILES ${CMAKE_CURRENT_BINARY_DIR}/share/kernel.json
              DESTINATION ${CMAKE_INSTALL_PREFIX}/share)
