# Signed growing-horizon sector bridge

Date: 2026-08-27 UTC

Claim labels: `machine-checked` for the T189 identities and conditional
consumer; `experiment` for every numerical value below. V1 remains a
`conjecture`.

## Exact checked bridge

For parent scale `q`, target `A`, horizons `N <= H`, and child digit `d < 10`,
write

```text
Z_d(M) = primitiveBoundaryFourierSum (10*q) (A+d*q) M,
Delta_0 = Re[(S_0(H)-S_0(N))],
Xi_d = Re sum_(n in [N,H)) sum_(1 <= r <= 9)
  exp(-2*pi*i*d*r/10) exp(2*pi*i*r*a_n/10)
  H_(q,r)(x_(n+1)-c_(q,A)).
```

Here `a_n` is the actual predecessor decimal digit of pi, `x_(n+1)` its
actual suffix orbit, and `H_(q,r)` is T179's finite predecessor-suffix kernel
with the literal boundary coefficients. T189 machine-checks

```text
10 * Re[Z_d(H)-Z_d(N)] = Delta_0 + Xi_d.
```

It also checks that `Delta_0` is exactly the parent-score increment plus the
T172 left-extension-remainder increment. Its final theorem is the direct
one-sided consumer: if the old child score plus these two fresh-block sectors
beats the T176 potential at `H`, then the child has positive signed prefix
surplus at `H`.

This theorem does not estimate `Xi_d`. Its value is that no unsigned norm,
zero-sector average, or unspecified child remains between the missing
pi-arithmetic input and the checked consumer.

## First candidate instance

The current experimental instance is

```text
q=1000, A=334, N=10000, H=100000, d=3,
c_(q,A)=669/2000.
```

The directly sufficient inequality is

```text
Xi_3 > -Delta_0 - 10*Re Z_3(10000) + 7/300.
```

It implies

```text
Re Z_3(100000) > 7/3000,
```

which is positive T176 surplus at a consumer-valid horizon.

Independent floating-point diagnostics give

```text
Re Z_parent(10000)   ~=  19.0156236884
Re Z_parent(100000)  ~=  -9.396426011
Re Z_3(10000)        ~=   3.026555854
Re Z_3(100000)       ~=   4.501761616
```

Using the exact T172 block-remainder bound, `Delta_0` lies approximately in
`[-28.60105,-28.22305]`. Consequently the exact sufficient threshold above
lies approximately between `-2.0192` and `-1.6412`; when only that remainder
bound is used, the uniform sufficient condition is the worse endpoint
`Xi_3 > -1.6411755067`. The observed child
increment forces `Xi_3` approximately into `[42.975,43.353]`, leaving a very
large experimental margin of more than `44.6`. These decimals are not
certificates.

## Narrow negative result and next lemma

The parent increment is about `-28.41205`; it even misses the previously
proposed coarse parent threshold near `-18.78227`. The zero sector averages
all ten children and is negative at `H`. Therefore parent-only or zero-sector
transport cannot explain this successful child. The fresh target sign is in
the nonzero character factor `exp(-2*pi*i*3*r/10)` coupled to the actual
predecessor digit and suffix.

The next mathematical task is not a larger finite payload. It is a rigorous
lower bound for the displayed `Xi_3` correlation, followed by a structural
mechanism that supplies analogous favorable fresh-block information on an
unbounded sequence of scales. Every proposed lemma must say where that new
target-signed information for `N <= n < H` enters.

## Finite-certificate cost checkpoint

The existing T187 ten-orbit shard is reproducible byte-for-byte. A focused
one-orbit Lean audit took about 48 seconds and 6.74 GiB; extrapolation of the
current representation gives a lower bound near 134 CPU-hours and roughly
113 GB of `.olean` output for all 10,000 orbit points. No full payload was
started. This checkpoint supports the decision to concentrate on the signed
horizon lemma rather than expanding certificate infrastructure.
