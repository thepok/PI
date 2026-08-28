#include <gmpxx.h>
#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <string>
#include <tuple>

// Exact Chudnovsky binary splitting.  No floating-point arithmetic is used.
// For [a,b), T/Q is the corresponding partial Chudnovsky sum.
struct BS {
  mpz_class P, Q, T;
};

static const mpz_class C3_OVER_24("10939058860032000");

BS bs(unsigned long a, unsigned long b) {
  if (b - a == 1) {
    BS r;
    if (a == 0) {
      r.P = 1;
      r.Q = 1;
    } else {
      mpz_class aa = a;
      r.P = (6 * aa - 5) * (2 * aa - 1) * (6 * aa - 1);
      r.Q = aa * aa * aa * C3_OVER_24;
    }
    r.T = r.P * (mpz_class(13591409) + mpz_class(545140134) * a);
    if (a & 1UL) r.T = -r.T;
    return r;
  }
  unsigned long m = (a + b) / 2;
  BS l = bs(a, m);
  BS r = bs(m, b);
  BS out;
  out.P = l.P * r.P;
  out.Q = l.Q * r.Q;
  out.T = l.T * r.Q + l.P * r.T;
  return out;
}

// Compare positive rationals a/b and c/d.
int cmp_rat(const mpz_class& a, const mpz_class& b,
            const mpz_class& c, const mpz_class& d) {
  return cmp(a * d, c * b);
}

mpz_class floor_rat(const mpz_class& num, const mpz_class& den) {
  mpz_class q;
  mpz_fdiv_q(q.get_mpz_t(), num.get_mpz_t(), den.get_mpz_t());
  return q;
}

int main(int argc, char** argv) {
  const unsigned long D = argc > 1 ? std::strtoul(argv[1], nullptr, 10) : 100050UL;
  const unsigned long N = argc > 2 ? std::strtoul(argv[2], nullptr, 10) : 7154UL;
  const unsigned long GUARD = 120UL;
  const unsigned long G = D + GUARD;

  BS n = bs(0, N);
  BS n1 = bs(0, N + 1);

  // Alternating, strictly decreasing Chudnovsky terms imply S lies strictly
  // between these two consecutive partial sums.  We still order them by an
  // exact cross multiplication rather than relying on N's parity.
  mpz_class Slo_num, Slo_den, Shi_num, Shi_den;
  if (cmp_rat(n.T, n.Q, n1.T, n1.Q) < 0) {
    Slo_num = n.T; Slo_den = n.Q;
    Shi_num = n1.T; Shi_den = n1.Q;
  } else {
    Slo_num = n1.T; Slo_den = n1.Q;
    Shi_num = n.T; Shi_den = n.Q;
  }

  mpz_class tenG;
  mpz_ui_pow_ui(tenG.get_mpz_t(), 10UL, G);
  mpz_class sqrtRad = mpz_class(10005) * tenG * tenG;
  mpz_class sqrtLo;
  mpz_sqrt(sqrtLo.get_mpz_t(), sqrtRad.get_mpz_t());
  mpz_class sqrtHi = sqrtLo + 1;

  // pi = 426880*sqrt(10005)/S.  Monotonicity gives exact rational bounds.
  mpz_class piLo_num = mpz_class(426880) * sqrtLo * Shi_den;
  mpz_class piLo_den = tenG * Shi_num;
  mpz_class piHi_num = mpz_class(426880) * sqrtHi * Slo_den;
  mpz_class piHi_den = tenG * Slo_num;

  mpz_class tenD;
  mpz_ui_pow_ui(tenD.get_mpz_t(), 10UL, D);
  mpz_class Plo = floor_rat(piLo_num * tenD, piLo_den);
  mpz_class Phi = floor_rat(piHi_num * tenD, piHi_den);

  if (Plo != Phi) {
    std::cerr << "FAIL: pi bounds do not determine D digits\n";
    std::cerr << "Plo=" << Plo << "\nPhi=" << Phi << "\n";
    return 2;
  }

  std::string digits = Plo.get_str();
  if (digits.size() != D + 1 || digits[0] != '3') {
    std::cerr << "FAIL: unexpected decimal length/prefix\n";
    return 3;
  }

  std::ofstream f("pi_digits_cert.txt", std::ios::binary);
  f << digits << "\n";
  f.close();

  // Exact checks used by the mathematical audit.
  const mpz_class lhs = mpz_class(6 * 6 * 6 * 6 * 6 * 6) * 42;
  mpz_class rhs = mpz_class(640320) * 640320 * 640320;
  if (!(lhs < rhs)) {
    std::cerr << "FAIL: simple monotone-term ratio bound\n";
    return 4;
  }
  if (!(sqrtLo * sqrtLo <= sqrtRad && sqrtRad < sqrtHi * sqrtHi)) {
    std::cerr << "FAIL: sqrt enclosure\n";
    return 5;
  }
  if (!(piLo_num * piHi_den < piHi_num * piLo_den)) {
    std::cerr << "FAIL: pi interval orientation\n";
    return 6;
  }

  std::cout << "claim=exact_integer_certificate\n";
  std::cout << "decimal_places=" << D << "\n";
  std::cout << "chudnovsky_terms_N=" << N << "\n";
  std::cout << "guard_places=" << GUARD << "\n";
  std::cout << "floor_10D_pi_digits=" << digits.size() << "\n";
  std::cout << "floor_10D_pi_prefix=" << digits.substr(0, 65) << "\n";
  std::cout << "floor_10D_pi_suffix=" << digits.substr(digits.size() - 64) << "\n";
  std::cout << "floor_10D_pi_file=pi_digits_cert.txt\n";
  std::cout << "cylinder_lower=P/10^D\n";
  std::cout << "cylinder_upper=(P+1)/10^D\n";
  std::cout << "proof_note=pi is strictly inside the displayed cylinder\n";
  return 0;
}
