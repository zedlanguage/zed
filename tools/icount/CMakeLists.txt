# The DynamoRIO client zed_icount (zed_icount.c says what it does). Built by build.sh.
cmake_minimum_required(VERSION 3.10)
# CXX too: DynamoRIO 11.3.0's DrMemoryFrameworkConfig.cmake, which DynamoRIOConfig.cmake loads, tests
# ${CMAKE_CXX_SIZEOF_DATA_PTR} unquoted and stops with "Unknown arguments" when it is unset.
project(zed_icount C CXX)
find_package(DynamoRIO REQUIRED)
add_library(zed_icount SHARED zed_icount.c)
configure_DynamoRIO_client(zed_icount)
use_DynamoRIO_extension(zed_icount drmgr)
use_DynamoRIO_extension(zed_icount drreg)
use_DynamoRIO_extension(zed_icount drcontainers)
find_package(Threads REQUIRED)
add_executable(zed_icount_selftest selftest.c)
target_link_libraries(zed_icount_selftest Threads::Threads)
