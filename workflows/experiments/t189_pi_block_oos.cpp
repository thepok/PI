// Double-precision experiment: replay disjoint actual-pi T189 blocks.
// This is a falsification aid, not a directed certificate or proof.
#include <cmath>
#include <cstdio>
#include <cstdlib>

static constexpr double PI = 3.141592653589793238462643383279502884;

static double alpha_h(int h) {
  const double Q = 10000.0;
  const double c = std::cos(PI / Q);
  double fejer, edge;
  if (h <= 10000) {
    fejer = (4 * Q * Q * Q + 2 * Q - 6 * Q * h * static_cast<double>(h)
             + 3 * h * static_cast<double>(h) * h - 3 * h) / (6 * Q * Q);
    edge = (3.0 * h - 2 * Q) / (2 * Q * Q);
  } else {
    fejer = ((2 * Q - h - 1) * (2 * Q - h) * (2 * Q - h + 1))
             / (6 * Q * Q);
    edge = (2 * Q - h) / (2 * Q * Q);
  }
  return (1 - c) * fejer + edge;
}

static double xi_step(double x) {
  const double Q = 10000.0;
  const double t = x - 0.33345;
  const double s = std::sin(PI * t);
  const double zero =
      (2 * (Q * Q - 1) - (2 * Q * Q + 1) * std::cos(PI / Q)) / (3 * Q);
  const double boundary =
      (std::cos(2 * PI * t) - std::cos(PI / Q))
      * std::pow(std::pow(std::sin(PI * Q * t), 2) / (Q * s * s), 2);
  double multiples = 0;
  for (int ell = 1; ell < 2000; ++ell) {
    const int h = 10 * ell;
    multiples += alpha_h(h) * std::cos(2 * PI * h * t);
  }
  return 10 * ((boundary - zero) / 2 - multiples);
}

int main() {
  const char *path = "../AllMath/workflows/research/pi/data/pi_digits_1048596.txt";
  FILE *file = std::fopen(path, "r");
  if (!file) return 2;
  auto *digits = static_cast<unsigned char *>(std::malloc(1050000));
  int length = 0, ch;
  while ((ch = std::fgetc(file)) != EOF)
    if ('0' <= ch && ch <= '9') digits[length++] = static_cast<unsigned char>(ch - '0');
  std::fclose(file);
  if (length < 190018) return 3;

  for (int block = 0; block < 18; ++block) {
    const int start = 10000 + block * 10000;
    const int end = start + 10000;
    double xi = 0, local = 0, hit = 0, other = 0, moment1 = 0, moment2 = 0;
    int signed_count = 0, count3334 = 0, count_a334 = 0;
    for (int n = start; n < end; ++n) {
      double x = 0, scale = 0.1;
      for (int j = 0; j < 18; ++j) {
        x += digits[n + j] * scale;
        scale *= 0.1;
      }
      const double value = xi_step(x);
      xi += value;
      const double centered = x - 0.33345;
      moment1 += centered;
      moment2 += centered * centered;
      if (digits[n + 1] == 3 && digits[n + 2] == 3 && digits[n + 3] == 4) {
        local += value;
        if (digits[n] == 3) {
          ++count3334;
          signed_count += 9;
          hit += value;
        } else {
          ++count_a334;
          --signed_count;
          other += value;
        }
      }
    }
    std::printf(
        "b=%02d [%d,%d) xi=% .9f count=%d c3334=%d ca334=%d "
        "local=% .9f hit=% .9f other=% .9f m1=% .3f m2=%.3f\n",
        block, start, end, xi, signed_count, count3334, count_a334,
        local, hit, other, moment1, moment2);
  }
  std::free(digits);
}
