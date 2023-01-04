set(OPENSSL_SOURCE_DIR  ${CMAKE_CURRENT_SOURCE_DIR}/third_party/openssl) # default path by CMake

include(ExternalProject)
# 如果在MacOSX上编译失败, 可设置环境变量export SDKROOT="$(xcrun --sdk macosx --show-sdk-path)", 本质只是用
# cmake来执行config make的过程
ExternalProject_Add(
  libopenssl
  SOURCE_DIR ${OPENSSL_SOURCE_DIR}
  CONFIGURE_COMMAND ./config
  BUILD_IN_SOURCE TRUE
  BUILD_COMMAND make -j
  EXCLUDE_FROM_ALL TRUE
  TEST_COMMAND ""
  INSTALL_COMMAND ""
  INSTALL_DIR ""
  )

# set for find openssl
set(OPENSSL_INCLUDE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/include)
set(OPENSSL_CRYPTO_LIBRARY ${CMAKE_CURRENT_SOURCE_DIR}/libcrypto.a)

ExternalProject_Get_Property(libopenssl source_dir)

add_library(OpenSSL::Crypto UNKNOWN IMPORTED)
add_dependencies(OpenSSL::Crypto libopenssl)
set_target_properties(OpenSSL::Crypto PROPERTIES
  IMPORTED_LOCATION ${source_dir}/libcrypto.a
  INTERFACE_INCLUDE_DIRECTORIES ${source_dir}/include
)

find_package(OpenSSL REQUIRED)
