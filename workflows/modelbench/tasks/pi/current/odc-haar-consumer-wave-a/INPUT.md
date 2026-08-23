# Frozen proposed theorem: moving-mesh collision plus approximate times-ten dynamics

Let `T = R/Z` with circle distance and let `S(x)=10x mod 1`. Let
`x_n in T`. Suppose there are integers `L_j -> infinity`, decimal meshes
`q_j=10^(k_j)` with `k_j -> infinity` and `q_j/L_j -> 0`, and a constant
`C<infinity` such that the following hold.

1. Approximate dynamics on every selected block:

   `eps_j := sup_{L_j <= n < 2L_j} dist_T(x_(n+1), S(x_n)) -> 0`.

2. For the half-open cells

   `I_(q,a)=[a/q,(a+1)/q)` for `0<=a<q`, put

   `n_j(a)=#{n in [L_j,2L_j): x_n in I_(q_j,a)}`.

   The moving-mesh collision bound is

   `sum_(a<q_j) n_j(a)^2 <= C*(L_j^2/q_j + L_j)`.

Proposed conclusion:

- the empirical block measures

  `mu_j=(1/L_j) sum_(n=L_j)^(2L_j-1) delta_(x_n)`

  converge weakly to Haar/Lebesgue probability measure on `T`;
- hence for every fixed integer `q>=2`, every cell `a<q`, and every index
  threshold `N0`, some sufficiently late selected block contains an
  `n>=N0` with `x_n` in the open interior `(a/q,(a+1)/q)`, so its canonical
  half-open cell is `a`.

Intended proof skeleton to audit, not assume:

1. Compactness gives weakly convergent subsequences.
2. For each fixed decimal mesh `Q=10^k`, eventually `Q|q_j`. Parent-cell
   Cauchy-Schwarz should give

   `Q*sum_(a<Q) mu_j(I_(Q,a))^2 <= C*(1+q_j/L_j)`.

3. Any weak limit has no atoms; decimal boundaries then have zero mass.
   Passing fixed-cell masses to the limit yields uniformly `L²`-bounded
   decimal conditional densities. A martingale argument should give an
   `L²` density with respect to Haar measure.
4. Approximate dynamics plus the two block endpoints should make every weak
   limit `S`-invariant.
5. If `mu=f dx`, `f in L²`, and `mu` is `S`-invariant, then
   `fhat(h)=fhat(10h)`. Square summability should force all nonzero Fourier
   coefficients to vanish, hence `mu=dx`.
6. If every subsequential weak limit is Haar, the full sequence converges.

Important boundaries:

- A liminf collision premise is usable only after selecting a subsequence and
  slightly enlarging its existential constant.
- The claim is generic and conditional. It does not prove the collision bound
  for the sampled BBP orbit or for pi.
- Existing work already studies fixed-pi long-lag collisions and Fejer
  majorants. Do not propose those as the missing proof. The only object under
  review here is this consumer theorem and its exact assumptions.
- For an eventual application, the sampled BBP recurrence supplies
  exponentially small errors in the approximate times-ten dynamics, but that
  fact is not a premise you need to rederive.

V1 remains open.
