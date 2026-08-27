// Double-precision experiment: matched order-four de Bruijn T189 separator.
// This is a falsification aid, not a directed certificate or proof.
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>

static constexpr double PI = 3.141592653589793238462643383279502884;
static std::uint64_t rng_state;

static std::uint64_t xorshift64() {
  rng_state ^= rng_state << 13;
  rng_state ^= rng_state >> 7;
  rng_state ^= rng_state << 17;
  return rng_state;
}

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

static int ipow(int base, int exponent) {
  int result = 1;
  while (exponent--) result *= base;
  return result;
}

static void debruijn(int order, int seed, int *word) {
  const int alphabet = 10;
  const int vertices = ipow(alphabet, order - 1);
  const int edges = ipow(alphabet, order);
  auto *adj = static_cast<int *>(std::malloc(vertices * alphabet * sizeof(int)));
  auto *pos = static_cast<int *>(std::calloc(vertices, sizeof(int)));
  auto *vertex_stack = static_cast<int *>(std::malloc((edges + 1) * sizeof(int)));
  auto *digit_stack = static_cast<int *>(std::malloc((edges + 1) * sizeof(int)));
  auto *reverse = static_cast<int *>(std::malloc(edges * sizeof(int)));
  rng_state = static_cast<std::uint64_t>(seed + 1234567);
  for (int v = 0; v < vertices; ++v) {
    for (int d = 0; d < alphabet; ++d) adj[v * alphabet + d] = d;
    for (int j = alphabet - 1; j > 0; --j) {
      const int z = static_cast<int>(xorshift64() % (j + 1));
      const int temp = adj[v * alphabet + j];
      adj[v * alphabet + j] = adj[v * alphabet + z];
      adj[v * alphabet + z] = temp;
    }
  }
  int top = 0, reversed_length = 0;
  vertex_stack[0] = 0;
  digit_stack[0] = -1;
  while (top >= 0) {
    const int v = vertex_stack[top];
    if (pos[v] < alphabet) {
      const int d = adj[v * alphabet + pos[v]++];
      ++top;
      vertex_stack[top] = (v * alphabet + d) % vertices;
      digit_stack[top] = d;
    } else {
      const int d = digit_stack[top--];
      if (d >= 0) reverse[reversed_length++] = d;
    }
  }
  for (int i = 0; i < edges; ++i) word[i] = reverse[edges - 1 - i];
  std::free(adj); std::free(pos); std::free(vertex_stack);
  std::free(digit_stack); std::free(reverse);
}

static double evaluate_cycle(const int *word, int period) {
  double total = 0;
  for (int i = 0; i < period; ++i) {
    double x = 0, scale = 0.1;
    for (int j = 0; j < 18; ++j) {
      x += word[(i + j) % period] * scale;
      scale *= 0.1;
    }
    total += xi_step(x);
  }
  return total;
}

static bool same_histograms_through_four(const int *left, const int *right,
                                         int period) {
  for (int length = 1, states = 10; length <= 4; ++length, states *= 10) {
    auto *left_count = static_cast<int *>(std::calloc(states, sizeof(int)));
    auto *right_count = static_cast<int *>(std::calloc(states, sizeof(int)));
    for (int i = 0; i < period; ++i) {
      int left_word = 0, right_word = 0;
      for (int j = 0; j < length; ++j) {
        left_word = 10 * left_word + left[(i + j) % period];
        right_word = 10 * right_word + right[(i + j) % period];
      }
      ++left_count[left_word];
      ++right_count[right_word];
    }
    for (int state = 0; state < states; ++state) {
      if (left_count[state] != right_count[state]) {
        std::free(left_count); std::free(right_count);
        return false;
      }
    }
    std::free(left_count); std::free(right_count);
  }
  return true;
}

int main() {
  const int order = 4, period = 10000;
  auto *word = static_cast<int *>(std::malloc(period * sizeof(int)));
  double minimum = 1e99, maximum = -1e99;
  int minimum_seed = -1, maximum_seed = -1, positive = 0, negative = 0;
  for (int seed = 0; seed < 40; ++seed) {
    debruijn(order, seed, word);
    const double value = evaluate_cycle(word, period);
    if (value < minimum) { minimum = value; minimum_seed = seed; }
    if (value > maximum) { maximum = value; maximum_seed = seed; }
    positive += value > 0;
    negative += value < 0;
  }
  std::printf(
      "order=%d P=%d lo=%.12g s=%d hi=%.12g s=%d pos=%d neg=%d\n",
      order, period, minimum, minimum_seed, maximum, maximum_seed,
      positive, negative);
  auto *negative_word = static_cast<int *>(std::malloc(period * sizeof(int)));
  auto *positive_word = static_cast<int *>(std::malloc(period * sizeof(int)));
  debruijn(order, 26, negative_word);
  debruijn(order, 10, positive_word);
  const bool histograms_equal =
      same_histograms_through_four(negative_word, positive_word, period);
  std::printf("seed26=%.12g seed10=%.12g histograms_L1_to_L4_equal=%s\n",
      evaluate_cycle(negative_word, period), evaluate_cycle(positive_word, period),
      histograms_equal ? "true" : "false");
  std::free(negative_word); std::free(positive_word);
  std::free(word);
  return histograms_equal ? 0 : 2;
}
