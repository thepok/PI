// Copy with: workflows/runtime/fastmath.sh new cpp work/my_search.cpp
// Run with:  workflows/runtime/fastmath.sh cpp work/my_search.cpp -- --self-test
//
// This template keeps the hot loop compiled and streaming. Replace
// evaluate_state with the problem-specific predicate, retain a tiny exact
// self-test, and write only independently checkable summaries/witnesses.

#include <charconv>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string_view>

struct Result {
  std::uint64_t processed = 0;
  std::uint64_t checksum = 0;
};

Result run_search(std::uint64_t limit) {
  Result result;
  for (std::uint64_t state = 0; state < limit; ++state) {
    // Deliberately simple known-answer kernel. Replace this expression.
    result.checksum += state * state;
    ++result.processed;
  }
  return result;
}

std::uint64_t parse_u64(std::string_view text) {
  std::uint64_t value = 0;
  const auto [end, error] =
      std::from_chars(text.data(), text.data() + text.size(), value);
  if (error != std::errc{} || end != text.data() + text.size()) {
    std::cerr << "invalid integer: " << text << '\n';
    std::exit(2);
  }
  return value;
}

int main(int argc, char** argv) {
  std::uint64_t limit = 10'000'000;
  bool self_test = false;
  for (int index = 1; index < argc; ++index) {
    const std::string_view arg(argv[index]);
    if (arg == "--self-test") {
      self_test = true;
    } else if (arg == "--limit" && index + 1 < argc) {
      limit = parse_u64(argv[++index]);
    } else {
      std::cerr << "usage: " << argv[0] << " [--self-test] [--limit N]\n";
      return 2;
    }
  }

  if (self_test) {
    const Result tiny = run_search(10);
    if (tiny.processed != 10 || tiny.checksum != 285) {
      std::cerr << "self-test failed\n";
      return 1;
    }
    std::cout << "{\"self_test\":true,\"processed\":10,\"checksum\":285}\n";
    return 0;
  }

  const auto start = std::chrono::steady_clock::now();
  const Result result = run_search(limit);
  const double seconds =
      std::chrono::duration<double>(std::chrono::steady_clock::now() - start)
          .count();
  std::cout << "{\"claim_label\":\"experiment\",\"processed\":"
            << result.processed << ",\"checksum\":" << result.checksum
            << ",\"seconds\":" << seconds << "}\n";
}
