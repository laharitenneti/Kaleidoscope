cmake_minimum_required(VERSION 3.13)
project(ToyCompiler LANGUAGES C CXX)

̐set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(LLVM REQUIRED CONFIG)
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")

add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

add_executable(toy
 src/main.cpp
 src/toy.cpp
)
llvm_map_components_to_libnames(llvm_libs core orcjit native)
target_link_libraries(toy ${llvm_libs})