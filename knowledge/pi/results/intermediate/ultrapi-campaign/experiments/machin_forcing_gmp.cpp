#include <gmpxx.h>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <deque>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

// Exact experiment for equation (11w) in ultrapi.md.  This is deliberately
// a finite computation, not a proof of any asymptotic or recurrence claim.

namespace fs = std::filesystem;

struct Options {
  unsigned long max_n = 1000;
  fs::path out_dir = "work/ultrapi-resume/experiments/data";
};

Options parse_options(int argc, char** argv) {
  Options options;
  for (int i = 1; i < argc; ++i) {
    const std::string arg = argv[i];
    if (arg == "--max-n" && i + 1 < argc) {
      options.max_n = std::stoul(argv[++i]);
    } else if (arg == "--out-dir" && i + 1 < argc) {
      options.out_dir = argv[++i];
    } else {
      throw std::runtime_error("unknown or incomplete argument: " + arg);
    }
  }
  return options;
}

mpz_class abs_z(const mpz_class& value) { return value >= 0 ? value : -value; }

mpz_class gcd_z(const mpz_class& left, const mpz_class& right) {
  mpz_class result;
  mpz_gcd(result.get_mpz_t(), left.get_mpz_t(), right.get_mpz_t());
  return result;
}

mpz_class lcm_z(const mpz_class& left, const mpz_class& right) {
  if (left == 0 || right == 0) return 0;
  const mpz_class common = gcd_z(left, right);
  return abs_z((left / common) * right);
}

unsigned long valuation(mpz_class value, const unsigned long prime) {
  value = abs_z(value);
  if (value == 0) throw std::runtime_error("valuation of zero requested");
  unsigned long result = 0;
  while (mpz_divisible_ui_p(value.get_mpz_t(), prime)) {
    mpz_divexact_ui(value.get_mpz_t(), value.get_mpz_t(), prime);
    ++result;
  }
  return result;
}

std::vector<unsigned long> distinct_prime_factors(unsigned long value) {
  std::vector<unsigned long> factors;
  for (unsigned long prime = 2; prime <= value / prime; ++prime) {
    if (value % prime != 0) continue;
    factors.push_back(prime);
    while (value % prime == 0) value /= prime;
  }
  if (value > 1) factors.push_back(value);
  return factors;
}

unsigned long pow_mod(unsigned long base, unsigned long exponent,
                      unsigned long modulus) {
  unsigned long result = 1 % modulus;
  unsigned long power = base % modulus;
  while (exponent > 0) {
    if (exponent & 1UL) {
      result = static_cast<unsigned long>(
          (static_cast<unsigned __int128>(result) * power) % modulus);
    }
    power = static_cast<unsigned long>(
        (static_cast<unsigned __int128>(power) * power) % modulus);
    exponent >>= 1;
  }
  return result;
}

mpq_class arctan_term(const unsigned long base, const unsigned long index) {
  const unsigned long exponent = 2 * index + 1;
  mpz_class base_power;
  mpz_ui_pow_ui(base_power.get_mpz_t(), base, exponent);
  const mpz_class denominator = mpz_class(exponent) * base_power;
  return mpq_class((index & 1UL) ? -1 : 1, denominator);
}

mpq_class initial_machin_lower() {
  mpq_class five = arctan_term(5, 0) + arctan_term(5, 1);
  mpq_class two_thirty_nine =
      arctan_term(239, 0) + arctan_term(239, 1) + arctan_term(239, 2);
  return 16 * five - 4 * two_thirty_nine;
}

void take_fractional_part(mpq_class& value) {
  mpz_class floor_value;
  mpz_fdiv_q(floor_value.get_mpz_t(), value.get_num_mpz_t(),
             value.get_den_mpz_t());
  value -= floor_value;
  if (value < 0 || value >= 1) {
    throw std::runtime_error("fractional-part reduction failed");
  }
}

unsigned long decimal_code(const mpq_class& orbit, unsigned long scale) {
  mpz_class scaled = orbit.get_num() * scale;
  mpz_class quotient;
  mpz_fdiv_q(quotient.get_mpz_t(), scaled.get_mpz_t(),
             orbit.get_den_mpz_t());
  return quotient.get_ui();
}

std::string factor_over_candidates(const mpz_class& input,
                                   const std::set<unsigned long>& candidates,
                                   bool* complete) {
  mpz_class remaining = abs_z(input);
  std::ostringstream output;
  bool first = true;
  for (const unsigned long prime : candidates) {
    unsigned long exponent = 0;
    while (mpz_divisible_ui_p(remaining.get_mpz_t(), prime)) {
      mpz_divexact_ui(remaining.get_mpz_t(), remaining.get_mpz_t(), prime);
      ++exponent;
    }
    if (exponent == 0) continue;
    if (!first) output << '*';
    output << prime;
    if (exponent > 1) output << '^' << exponent;
    first = false;
  }
  *complete = remaining == 1;
  if (remaining != 1) {
    if (!first) output << '*';
    output << "cofactor(" << remaining << ')';
  }
  return output.str();
}

int main(int argc, char** argv) {
  try {
    const Options options = parse_options(argc, argv);
    fs::create_directories(options.out_dir);
    std::ofstream rows(options.out_dir / "rows.tsv");
    std::ofstream small_exact(options.out_dir / "small_exact.tsv");
    std::ofstream gcd_events(options.out_dir / "gcd_events.tsv");
    std::ofstream criterion_mismatches(
        options.out_dir / "criterion_mismatches.tsv");
    if (!rows || !small_exact || !gcd_events || !criterion_mismatches) {
      throw std::runtime_error("could not open output files");
    }

    const std::vector<unsigned long> residue_primes =
        {17, 19, 29, 31, 43, 59, 101, 251, 1009};
    rows << "N\tnum_bits\tden_bits\tlambda_bits\tcancellation_g\tg_factorization"
            "\tv2_num\tv3_g";
    for (const auto prime : residue_primes) rows << "\tu_num_mod_" << prime;
    for (const auto prime : residue_primes) rows << "\tu_lcd_mod_" << prime;
    rows << "\tcode1\tcode2\tcode3\tcode4\n";
    small_exact << "N\tT\tLambda\tg\tdelta_num\tdelta_den\n";
    gcd_events << "N\tlag\tgcd_normalized_odd_numerators\n";
    criterion_mismatches << "N\tprime\tinterior_index\texponent\texpected\tactual\n";

    mpq_class orbit = initial_machin_lower();
    take_fractional_part(orbit);

    mpz_class power10 = 10;
    mpz_class power5_n_plus_1 = 5;
    mpz_class power5_start;
    mpz_ui_pow_ui(power5_start.get_mpz_t(), 5, 5);
    mpz_class power239_start;
    mpz_ui_pow_ui(power239_start.get_mpz_t(), 239, 7);
    mpz_class step5;
    mpz_ui_pow_ui(step5.get_mpz_t(), 5, 12);
    mpz_class step239;
    mpz_ui_pow_ui(step239.get_mpz_t(), 239, 12);
    const mpz_class five_squared = 25;
    const mpz_class two_thirty_nine_squared = mpz_class(239) * 239;

    std::vector<std::vector<bool>> seen = {
        std::vector<bool>(10), std::vector<bool>(100),
        std::vector<bool>(1000), std::vector<bool>(10000)};
    std::vector<unsigned long> seen_count(4, 0);
    std::vector<long> first_full(4, -1);
    const unsigned long scales[4] = {10, 100, 1000, 10000};

    std::deque<mpz_class> recent_odd_numerators;
    unsigned long positivity_failures = 0;
    unsigned long lambda_formula_failures = 0;
    unsigned long integer_sum_failures = 0;
    unsigned long v2_failures = 0;
    unsigned long v3_failures = 0;
    unsigned long factor_support_failures = 0;
    unsigned long criterion_failure_count = 0;
    unsigned long extra_cancellation_rows = 0;
    unsigned long composite_extra_rows = 0;
    unsigned long max_g_bits = 0;
    unsigned long max_odd_gcd_bits = 0;

    const auto started = std::chrono::steady_clock::now();
    for (unsigned long n = 0; n <= options.max_n; ++n) {
      unsigned long codes[4];
      for (std::size_t index = 0; index < 4; ++index) {
        codes[index] = decimal_code(orbit, scales[index]);
        if (!seen[index][codes[index]]) {
          seen[index][codes[index]] = true;
          ++seen_count[index];
          if (seen_count[index] == seen[index].size()) {
            first_full[index] = static_cast<long>(n);
          }
        }
      }

      std::vector<mpq_class> terms;
      terms.reserve(12);
      mpz_class lambda = 1;
      mpz_class lambda_formula = 1;
      mpz_class p5 = power5_start;
      mpz_class p239 = power239_start;
      std::set<unsigned long> factor_candidates = {2, 3, 5, 7, 11, 13, 239};
      std::map<unsigned long, std::pair<unsigned long, unsigned long>>
          interior_prime_location;

      for (unsigned long j = 0; j < 6; ++j) {
        const unsigned long a = 12 * n + 5 + 2 * j;
        const unsigned long b = a + 2;
        const int sign = (j & 1UL) ? -1 : 1;
        mpq_class term5(mpz_class(sign) * 16 * power10, mpz_class(a) * p5);
        mpq_class term239(mpz_class(sign) * 4 * power10,
                           mpz_class(b) * p239);
        // GMP's numerator/denominator constructor does not promise a
        // canonical representation.  Lambda_N is defined from individually
        // reduced terms, so canonicalization here is mathematically material.
        term5.canonicalize();
        term239.canonicalize();
        terms.push_back(term5);
        terms.push_back(term239);
        lambda = lcm_z(lambda, term5.get_den());
        lambda = lcm_z(lambda, term239.get_den());

        const mpz_class d5 = (mpz_class(a) * p5) / power5_n_plus_1;
        unsigned long stripped_b = b;
        unsigned long remaining_fives = n + 1;
        while (remaining_fives > 0 && stripped_b % 5 == 0) {
          stripped_b /= 5;
          --remaining_fives;
        }
        const mpz_class d239 = mpz_class(stripped_b) * p239;
        lambda_formula = lcm_z(lambda_formula, d5);
        lambda_formula = lcm_z(lambda_formula, d239);
        if (term5.get_den() != d5 || term239.get_den() != d239) {
          ++lambda_formula_failures;
        }

        for (const auto prime : distinct_prime_factors(a)) {
          factor_candidates.insert(prime);
          if (j >= 1 && j <= 5 && prime >= 17 && prime != 239) {
            interior_prime_location[prime] = {j, a};
          }
        }
        if (j == 5) {
          for (const auto prime : distinct_prime_factors(b)) {
            factor_candidates.insert(prime);
          }
        }
        p5 *= five_squared;
        p239 *= two_thirty_nine_squared;
      }
      if (lambda != lambda_formula) ++lambda_formula_failures;

      mpq_class delta = 0;
      mpz_class integer_sum = 0;
      for (const auto& term : terms) {
        delta += term;
        const mpz_class multiplier = lambda / term.get_den();
        integer_sum += term.get_num() * multiplier;
      }
      if (delta <= 0) ++positivity_failures;
      const mpz_class T = delta.get_num() * (lambda / delta.get_den());
      if (T != integer_sum) ++integer_sum_failures;
      const mpz_class g = gcd_z(abs_z(T), lambda);
      if (delta.get_num() != T / g || delta.get_den() != lambda / g) {
        ++integer_sum_failures;
      }

      const unsigned long v2_num = valuation(delta.get_num(), 2);
      const unsigned long v3_g = valuation(g, 3);
      if (v2_num != n + 4) ++v2_failures;
      if (v3_g != 1) ++v3_failures;
      if (g != 3) ++extra_cancellation_rows;
      max_g_bits = std::max(max_g_bits,
                            static_cast<unsigned long>(mpz_sizeinbase(g.get_mpz_t(), 2)));

      bool factorization_complete = false;
      const std::string g_factorization =
          factor_over_candidates(g, factor_candidates, &factorization_complete);
      if (!factorization_complete) ++factor_support_failures;
      mpz_class extra = g / 3;
      if (extra > 1 && mpz_probab_prime_p(extra.get_mpz_t(), 25) == 0) {
        ++composite_extra_rows;
      }

      for (const auto& [prime, location] : interior_prime_location) {
        const unsigned long j = location.first;
        const unsigned long a = location.second;
        const unsigned long lhs = static_cast<unsigned long>(
            (4ULL * pow_mod(239, a, prime)) % prime);
        const unsigned long rhs = pow_mod(5, a, prime);
        const bool expected = lhs == rhs;
        const bool actual = mpz_divisible_ui_p(g.get_mpz_t(), prime);
        if (expected != actual) {
          ++criterion_failure_count;
          criterion_mismatches << n << '\t' << prime << '\t' << j << '\t'
                               << a << '\t' << expected << '\t' << actual << '\n';
        }
      }

      mpz_class odd_numerator = delta.get_num();
      mpz_tdiv_q_2exp(odd_numerator.get_mpz_t(), odd_numerator.get_mpz_t(),
                      n + 4);
      mpz_class odd_lcd_numerator = T;
      mpz_tdiv_q_2exp(odd_lcd_numerator.get_mpz_t(),
                      odd_lcd_numerator.get_mpz_t(), n + 4);
      if (!mpz_odd_p(odd_numerator.get_mpz_t()) ||
          !mpz_odd_p(odd_lcd_numerator.get_mpz_t())) {
        ++v2_failures;
      }

      for (std::size_t lag = 1; lag <= recent_odd_numerators.size(); ++lag) {
        const mpz_class common = gcd_z(
            odd_numerator,
            recent_odd_numerators[recent_odd_numerators.size() - lag]);
        if (common > 1) {
          gcd_events << n << '\t' << lag << '\t' << common << '\n';
          max_odd_gcd_bits = std::max(
              max_odd_gcd_bits,
              static_cast<unsigned long>(mpz_sizeinbase(common.get_mpz_t(), 2)));
        }
      }
      recent_odd_numerators.push_back(odd_numerator);
      if (recent_odd_numerators.size() > 10) recent_odd_numerators.pop_front();

      rows << n << '\t' << mpz_sizeinbase(delta.get_num_mpz_t(), 2) << '\t'
           << mpz_sizeinbase(delta.get_den_mpz_t(), 2) << '\t'
           << mpz_sizeinbase(lambda.get_mpz_t(), 2) << '\t' << g << '\t'
           << g_factorization << '\t' << v2_num << '\t' << v3_g;
      for (const auto prime : residue_primes) {
        rows << '\t' << mpz_fdiv_ui(odd_numerator.get_mpz_t(), prime);
      }
      for (const auto prime : residue_primes) {
        rows << '\t' << mpz_fdiv_ui(odd_lcd_numerator.get_mpz_t(), prime);
      }
      for (const auto code : codes) rows << '\t' << code;
      rows << '\n';

      if (n <= 20) {
        small_exact << n << '\t' << T << '\t' << lambda << '\t' << g << '\t'
                    << delta.get_num() << '\t' << delta.get_den() << '\n';
      }

      orbit = 10 * orbit + delta;
      take_fractional_part(orbit);
      power10 *= 10;
      power5_n_plus_1 *= 5;
      power5_start *= step5;
      power239_start *= step239;

      if ((n + 1) % 1000 == 0 || n == options.max_n) {
        const auto elapsed = std::chrono::duration<double>(
            std::chrono::steady_clock::now() - started).count();
        std::cerr << "completed N=" << n << " elapsed_s=" << elapsed << '\n';
      }
    }

    const auto elapsed = std::chrono::duration<double>(
        std::chrono::steady_clock::now() - started).count();
    std::ofstream summary(options.out_dir / "summary.json");
    summary << "{\n"
            << "  \"claim_status\": \"experiment\",\n"
            << "  \"max_n\": " << options.max_n << ",\n"
            << "  \"row_count\": " << options.max_n + 1 << ",\n"
            << "  \"elapsed_seconds\": " << elapsed << ",\n"
            << "  \"positivity_failures\": " << positivity_failures << ",\n"
            << "  \"lambda_formula_failures\": " << lambda_formula_failures << ",\n"
            << "  \"integer_sum_failures\": " << integer_sum_failures << ",\n"
            << "  \"v2_failures\": " << v2_failures << ",\n"
            << "  \"v3_failures\": " << v3_failures << ",\n"
            << "  \"factor_support_failures\": " << factor_support_failures << ",\n"
            << "  \"large_prime_local_criterion_failures\": "
            << criterion_failure_count << ",\n"
            << "  \"extra_cancellation_rows\": " << extra_cancellation_rows << ",\n"
            << "  \"composite_extra_rows\": " << composite_extra_rows << ",\n"
            << "  \"max_cancellation_bits\": " << max_g_bits << ",\n"
            << "  \"max_nearby_odd_numerator_gcd_bits\": "
            << max_odd_gcd_bits << ",\n"
            << "  \"code_coverage\": [\n";
    for (std::size_t index = 0; index < 4; ++index) {
      summary << "    {\"digits\": " << index + 1
              << ", \"seen\": " << seen_count[index]
              << ", \"total\": " << seen[index].size()
              << ", \"first_full_N\": ";
      if (first_full[index] < 0) summary << "null";
      else summary << first_full[index];
      summary << '}' << (index + 1 == 4 ? "\n" : ",\n");
    }
    summary << "  ]\n}\n";
    std::cerr << "wrote " << options.out_dir << "\n";
    return 0;
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return 2;
  }
}
