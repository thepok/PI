#include <gmpxx.h>

#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>

// Finite exact audit of the reduced denominator of {10^n M_{3n}}.
// The output is experiment-level evidence only.

mpq_class arctan_term(const unsigned long base, const unsigned long index) {
  const unsigned long exponent = 2 * index + 1;
  mpz_class power;
  mpz_ui_pow_ui(power.get_mpz_t(), base, exponent);
  return mpq_class((index & 1UL) ? -1 : 1,
                   mpz_class(exponent) * power);
}

mpq_class initial_machin_lower() {
  const mpq_class five = arctan_term(5, 0) + arctan_term(5, 1);
  const mpq_class other =
      arctan_term(239, 0) + arctan_term(239, 1) + arctan_term(239, 2);
  return 16 * five - 4 * other;
}

void take_fractional_part(mpq_class& value) {
  mpz_class floor_value;
  mpz_fdiv_q(floor_value.get_mpz_t(), value.get_num_mpz_t(),
             value.get_den_mpz_t());
  value -= floor_value;
}

unsigned long valuation(mpz_class value, const unsigned long prime) {
  unsigned long result = 0;
  while (mpz_divisible_ui_p(value.get_mpz_t(), prime)) {
    mpz_divexact_ui(value.get_mpz_t(), value.get_mpz_t(), prime);
    ++result;
  }
  return result;
}

int main(int argc, char** argv) {
  try {
    if (argc != 3) {
      throw std::runtime_error("usage: program MAX_N OUTPUT.tsv");
    }
    const unsigned long max_n = std::stoul(argv[1]);
    std::ofstream output(argv[2]);
    if (!output) throw std::runtime_error("could not open output");
    output << "N\tnum_bits\tden_bits\tv5_den\tv239_den\n";

    mpq_class orbit = initial_machin_lower();
    take_fractional_part(orbit);
    mpz_class power10 = 10;
    mpz_class power5;
    mpz_class power239;
    mpz_ui_pow_ui(power5.get_mpz_t(), 5, 5);
    mpz_ui_pow_ui(power239.get_mpz_t(), 239, 7);
    mpz_class step5;
    mpz_class step239;
    mpz_ui_pow_ui(step5.get_mpz_t(), 5, 12);
    mpz_ui_pow_ui(step239.get_mpz_t(), 239, 12);

    for (unsigned long n = 0; n <= max_n; ++n) {
      output << n << '\t' << mpz_sizeinbase(orbit.get_num_mpz_t(), 2)
             << '\t' << mpz_sizeinbase(orbit.get_den_mpz_t(), 2)
             << '\t' << valuation(orbit.get_den(), 5)
             << '\t' << valuation(orbit.get_den(), 239) << '\n';

      mpq_class delta = 0;
      mpz_class p5 = power5;
      mpz_class p239 = power239;
      for (unsigned long local = 0; local < 6; ++local) {
        const unsigned long a = 12 * n + 5 + 2 * local;
        const unsigned long b = a + 2;
        const int sign = (local & 1UL) ? -1 : 1;
        delta += mpq_class(mpz_class(sign) * 16 * power10,
                           mpz_class(a) * p5);
        delta += mpq_class(mpz_class(sign) * 4 * power10,
                           mpz_class(b) * p239);
        p5 *= 25;
        p239 *= mpz_class(239) * 239;
      }
      orbit = 10 * orbit + delta;
      take_fractional_part(orbit);
      power10 *= 10;
      power5 *= step5;
      power239 *= step239;
      if ((n + 1) % 250 == 0 || n == max_n) {
        std::cerr << "completed N=" << n << '\n';
      }
    }
    return 0;
  } catch (const std::exception& error) {
    std::cerr << error.what() << '\n';
    return 2;
  }
}
