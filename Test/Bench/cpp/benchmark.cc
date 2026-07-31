#include "Perf.pb.h"

#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>

namespace {

using Batch = bench::perf::Batch;
using Clock = std::chrono::steady_clock;

constexpr std::uint64_t kFnvOffset = 14695981039346656037ULL;
constexpr std::uint64_t kFnvPrime = 1099511628211ULL;

std::uint64_t hash_byte(std::uint64_t hash, std::uint8_t byte) {
  return (hash ^ byte) * kFnvPrime;
}

std::uint64_t hash_u64(std::uint64_t hash, std::uint64_t value) {
  for (int i = 0; i < 8; ++i) {
    hash = hash_byte(hash, static_cast<std::uint8_t>(value));
    value >>= 8;
  }
  return hash;
}

std::uint64_t hash_bytes_with_length(std::uint64_t hash,
                                     std::string_view bytes) {
  hash = hash_u64(hash, bytes.size());
  for (unsigned char byte : bytes) {
    hash = hash_byte(hash, byte);
  }
  return hash;
}

std::uint64_t hash_bytes(std::string_view bytes) {
  std::uint64_t hash = kFnvOffset;
  for (unsigned char byte : bytes) {
    hash = hash_byte(hash, byte);
  }
  return hash;
}

std::uint64_t content_hash(const Batch& batch) {
  std::uint64_t hash = hash_bytes_with_length(kFnvOffset, batch.label());
  hash = hash_u64(hash, batch.items_size());
  for (const auto& item : batch.items()) {
    hash = hash_u64(hash, item.id());
    hash = hash_bytes_with_length(hash, item.name());
    hash = hash_u64(hash, item.scores_size());
    for (std::int32_t score : item.scores()) {
      hash = hash_u64(hash, static_cast<std::uint32_t>(score));
    }
    hash = hash_bytes_with_length(hash, item.payload());
    if (item.has_meta()) {
      hash = hash_byte(hash, 1);
      hash = hash_bytes_with_length(hash, item.meta().source());
      hash = hash_u64(hash, item.meta().created_at());
      hash = hash_byte(hash, item.meta().active() ? 1 : 0);
    } else {
      hash = hash_byte(hash, 0);
    }
    hash = hash_u64(hash, item.tags_size());
    for (const auto& tag : item.tags()) {
      hash = hash_bytes_with_length(hash, tag);
    }
    hash = hash_bytes_with_length(hash, item.note());
  }
  return hash;
}

Batch make_batch(std::uint64_t item_count) {
  if (item_count >
      static_cast<std::uint64_t>(std::numeric_limits<int>::max())) {
    throw std::runtime_error("item count is too large for the C++ runtime");
  }

  Batch batch;
  batch.set_label("batch-" + std::to_string(item_count));
  batch.mutable_items()->Reserve(static_cast<int>(item_count));
  for (std::uint64_t i = 0; i < item_count; ++i) {
    auto* item = batch.add_items();
    item->set_id(static_cast<std::uint32_t>(i));
    item->set_name("item-" + std::to_string(i));
    for (std::uint64_t j = 0; j < 8; ++j) {
      const auto score =
          static_cast<std::int64_t>((i + 1) * (j + 3)) - 19;
      item->add_scores(static_cast<std::int32_t>(score));
    }
    std::string payload;
    payload.reserve(48 + i % 16);
    for (std::uint64_t j = 0; j < 48 + i % 16; ++j) {
      payload.push_back(
          static_cast<char>((i * 31 + j * 17 + 13) % 251));
    }
    item->set_payload(std::move(payload));
    auto* metadata = item->mutable_meta();
    metadata->set_source("source-" + std::to_string(i % 11));
    metadata->set_created_at(1700000000ULL + i * 17);
    metadata->set_active(i % 2 == 0);
    item->add_tags("tag-" + std::to_string(i % 5));
    item->add_tags("group-" + std::to_string(i % 9));
    item->add_tags("bucket-" + std::to_string(i % 13));
    item->add_tags("region-" + std::to_string(i % 7));
    item->set_note("note-" + std::to_string(i % 17) + "-" +
                   std::to_string(i * 3));
  }
  return batch;
}

std::string encode(const Batch& batch) {
  std::string bytes;
  if (!batch.SerializeToString(&bytes)) {
    throw std::runtime_error("C++ protobuf serialization failed");
  }
  return bytes;
}

Batch decode(std::string_view bytes) {
  Batch batch;
  if (!batch.ParseFromArray(bytes.data(), static_cast<int>(bytes.size()))) {
    throw std::runtime_error("C++ protobuf parsing failed");
  }
  return batch;
}

std::uint64_t consume_bytes(std::string_view bytes) {
  if (bytes.empty()) {
    return 0;
  }
  return bytes.size() + static_cast<unsigned char>(bytes.front()) +
         static_cast<unsigned char>(bytes.back());
}

std::uint64_t consume_batch(const Batch& batch) {
  if (batch.items().empty()) {
    return batch.label().size();
  }
  return batch.items_size() + batch.items(0).id() +
         batch.items(batch.items_size() - 1).id() + batch.label().size();
}

std::uint64_t elapsed_ns(Clock::time_point start, Clock::time_point stop) {
  return std::chrono::duration_cast<std::chrono::nanoseconds>(stop - start)
      .count();
}

std::uint64_t parse_u64(const char* name, const char* value) {
  try {
    std::size_t consumed = 0;
    const auto parsed = std::stoull(value, &consumed);
    if (consumed != std::string(value).size()) {
      throw std::invalid_argument("trailing content");
    }
    return parsed;
  } catch (const std::exception&) {
    throw std::runtime_error(std::string("invalid ") + name + ": " + value);
  }
}

struct Result {
  std::uint64_t data_setup_ns = 0;
  std::uint64_t input_setup_ns = 0;
  std::uint64_t first_ns = 0;
  std::uint64_t steady_ns = 0;
  std::uint64_t output_bytes = 0;
  std::uint64_t content_hash = 0;
  std::uint64_t output_hash = 0;
  std::uint64_t checksum = 0;
};

void print_result(std::string_view operation, std::uint64_t items,
                  std::uint64_t iterations, bool validate,
                  const Result& result) {
  const auto ns_per_op =
      iterations == 0 ? 0 : result.steady_ns / iterations;
  std::cout << "BENCH_RESULT implementation=cpp-binary"
            << " operation=" << operation << " items=" << items
            << " iterations=" << iterations
            << " data_setup_ns=" << result.data_setup_ns
            << " input_setup_ns=" << result.input_setup_ns
            << " first_ns=" << result.first_ns
            << " steady_ns=" << result.steady_ns
            << " steady_ns_per_op=" << ns_per_op
            << " output_bytes=" << result.output_bytes
            << " content_hash=" << result.content_hash
            << " output_hash=" << result.output_hash
            << " checksum=" << result.checksum
            << " validation=" << (validate ? 1 : 0)
            << " runtime_version=" << GOOGLE_PROTOBUF_VERSION << '\n';
}

Result run_encode(std::uint64_t items, std::uint64_t iterations,
                  bool validate) {
  Result result;
  auto start = Clock::now();
  Batch batch = make_batch(items);
  auto stop = Clock::now();
  result.data_setup_ns = elapsed_ns(start, stop);
  result.content_hash = content_hash(batch);

  start = Clock::now();
  std::string last = encode(batch);
  stop = Clock::now();
  result.first_ns = elapsed_ns(start, stop);
  result.checksum = consume_bytes(last);

  start = Clock::now();
  for (std::uint64_t i = 0; i < iterations; ++i) {
    std::string bytes = encode(batch);
    result.checksum += consume_bytes(bytes);
    last = std::move(bytes);
  }
  stop = Clock::now();
  result.steady_ns = elapsed_ns(start, stop);

  if (validate) {
    const Batch decoded = decode(last);
    const auto actual_hash = content_hash(decoded);
    if (actual_hash != result.content_hash) {
      throw std::runtime_error("cpp-binary encode content mismatch");
    }
  }
  result.output_bytes = last.size();
  result.output_hash = hash_bytes(last);
  return result;
}

Result run_decode(std::uint64_t items, std::uint64_t iterations,
                  bool validate) {
  Result result;
  auto start = Clock::now();
  Batch batch = make_batch(items);
  auto stop = Clock::now();
  result.data_setup_ns = elapsed_ns(start, stop);
  result.content_hash = content_hash(batch);

  start = Clock::now();
  const std::string input = encode(batch);
  stop = Clock::now();
  result.input_setup_ns = elapsed_ns(start, stop);

  start = Clock::now();
  Batch last = decode(input);
  stop = Clock::now();
  result.first_ns = elapsed_ns(start, stop);
  result.checksum = consume_batch(last);

  start = Clock::now();
  for (std::uint64_t i = 0; i < iterations; ++i) {
    Batch decoded = decode(input);
    result.checksum += consume_batch(decoded);
    last = std::move(decoded);
  }
  stop = Clock::now();
  result.steady_ns = elapsed_ns(start, stop);

  if (validate && content_hash(last) != result.content_hash) {
    throw std::runtime_error("cpp-binary decode content mismatch");
  }
  result.output_bytes = input.size();
  result.output_hash = hash_bytes(input);
  return result;
}

}  // namespace

int main(int argc, char** argv) {
  try {
    if (argc == 2 && std::string_view(argv[1]) == "startup") {
      std::cout
          << "BENCH_RESULT implementation=cpp-runtime operation=startup "
             "items=0 iterations=0 data_setup_ns=0 input_setup_ns=0 first_ns=0 "
             "steady_ns=0 steady_ns_per_op=0 output_bytes=0 content_hash=0 "
             "output_hash=0 checksum=0 validation=0 runtime_version="
          << GOOGLE_PROTOBUF_VERSION << '\n';
      return 0;
    }
    if (argc == 2 && std::string_view(argv[1]) == "version") {
      std::cout << BENCH_PROTOBUF_RELEASE << " " << GOOGLE_PROTOBUF_VERSION
                << '\n';
      return 0;
    }
    if (argc != 5) {
      throw std::runtime_error(
          "usage: <encode|decode> <items> <steady-iterations> <validate:0|1>");
    }
    const std::string_view operation = argv[1];
    const auto items = parse_u64("items", argv[2]);
    const auto iterations = parse_u64("steady-iterations", argv[3]);
    const auto validate_number = parse_u64("validate", argv[4]);
    if (validate_number > 1) {
      throw std::runtime_error("validate must be 0 or 1");
    }
    const bool validate = validate_number == 1;
    if (operation == "encode") {
      print_result(operation, items, iterations, validate,
                   run_encode(items, iterations, validate));
    } else if (operation == "decode") {
      print_result(operation, items, iterations, validate,
                   run_decode(items, iterations, validate));
    } else {
      throw std::runtime_error("operation must be encode or decode");
    }
    return 0;
  } catch (const std::exception& error) {
    std::cerr << "benchmark error: " << error.what() << '\n';
    return 2;
  }
}
