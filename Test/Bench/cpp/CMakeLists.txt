cmake_minimum_required(VERSION 3.16)
project(protobuf_lean_benchmark LANGUAGES CXX)

include(FetchContent)

set(BENCH_PROTOBUF_VERSION "35.0" CACHE STRING "Pinned protobuf release")
set(
  BENCH_PROTOBUF_SOURCE_SHA256
  "e127ea69dd7be4e88abdd95845fb6c30d25d96971d95827e92b70e2e910d46a1"
  CACHE STRING
  "SHA-256 of the pinned protobuf source archive"
)
set(BENCH_PROTOC "" CACHE FILEPATH "protoc matching BENCH_PROTOBUF_VERSION")
set(BENCH_PROTO_FILE "${CMAKE_CURRENT_LIST_DIR}/../Perf.proto")

if(NOT BENCH_PROTOC)
  message(FATAL_ERROR "BENCH_PROTOC must name protoc ${BENCH_PROTOBUF_VERSION}")
endif()

execute_process(
  COMMAND "${BENCH_PROTOC}" --version
  OUTPUT_VARIABLE BENCH_PROTOC_VERSION
  OUTPUT_STRIP_TRAILING_WHITESPACE
  RESULT_VARIABLE BENCH_PROTOC_STATUS
)
if(NOT BENCH_PROTOC_STATUS EQUAL 0)
  message(FATAL_ERROR "failed to run BENCH_PROTOC=${BENCH_PROTOC}")
endif()
if(NOT BENCH_PROTOC_VERSION STREQUAL "libprotoc ${BENCH_PROTOBUF_VERSION}")
  message(FATAL_ERROR
    "BENCH_PROTOC is ${BENCH_PROTOC_VERSION}; expected libprotoc ${BENCH_PROTOBUF_VERSION}")
endif()

set(protobuf_BUILD_TESTS OFF CACHE BOOL "" FORCE)
set(protobuf_BUILD_CONFORMANCE OFF CACHE BOOL "" FORCE)
set(protobuf_BUILD_EXAMPLES OFF CACHE BOOL "" FORCE)
set(protobuf_BUILD_PROTOC_BINARIES OFF CACHE BOOL "" FORCE)
set(protobuf_BUILD_LIBPROTOC OFF CACHE BOOL "" FORCE)
set(protobuf_BUILD_LIBUPB OFF CACHE BOOL "" FORCE)
set(protobuf_INSTALL OFF CACHE BOOL "" FORCE)
set(protobuf_WITH_ZLIB OFF CACHE BOOL "" FORCE)
set(protobuf_BUILD_SHARED_LIBS OFF CACHE BOOL "" FORCE)
set(protobuf_FORCE_FETCH_DEPENDENCIES ON CACHE BOOL "" FORCE)
set(ABSL_PROPAGATE_CXX_STD ON CACHE BOOL "" FORCE)

FetchContent_Declare(
  protobuf
  URL "https://github.com/protocolbuffers/protobuf/archive/refs/tags/v${BENCH_PROTOBUF_VERSION}.tar.gz"
  URL_HASH "SHA256=${BENCH_PROTOBUF_SOURCE_SHA256}"
)
FetchContent_MakeAvailable(protobuf)

set(BENCH_GENERATED_DIR "${CMAKE_CURRENT_BINARY_DIR}/generated")
set(BENCH_GENERATED_CC "${BENCH_GENERATED_DIR}/Perf.pb.cc")
set(BENCH_GENERATED_H "${BENCH_GENERATED_DIR}/Perf.pb.h")

add_custom_command(
  OUTPUT "${BENCH_GENERATED_CC}" "${BENCH_GENERATED_H}"
  COMMAND "${CMAKE_COMMAND}" -E make_directory "${BENCH_GENERATED_DIR}"
  COMMAND
    "${BENCH_PROTOC}"
    "--proto_path=${CMAKE_CURRENT_LIST_DIR}/.."
    "--cpp_out=${BENCH_GENERATED_DIR}"
    "${BENCH_PROTO_FILE}"
  DEPENDS "${BENCH_PROTO_FILE}"
  VERBATIM
)

add_executable(
  benchCppCodec
  benchmark.cc
  "${BENCH_GENERATED_CC}"
  "${BENCH_GENERATED_H}"
)
target_compile_features(benchCppCodec PRIVATE cxx_std_17)
target_compile_definitions(
  benchCppCodec PRIVATE
  BENCH_PROTOBUF_RELEASE="${BENCH_PROTOBUF_VERSION}"
)
target_include_directories(benchCppCodec PRIVATE "${BENCH_GENERATED_DIR}")
target_link_libraries(benchCppCodec PRIVATE protobuf::libprotobuf)
