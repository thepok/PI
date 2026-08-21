# T31: a disjunctive decimal stream with maximal subsequential resonance

Status: `proof sketch` (self-contained written proof, not machine-checked)

## Provenance

- Canonical source: `knowledge/pi/statements/pi-digits.txt`
- Canonical source SHA-256:
  `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
- Original source URL: none is recorded in the immutable local source.
- Agenda item: T31, serving G20.

The canonical source asks V1 only for the decimal expansion of pi. The object
constructed below is an artificial decimal stream. It is used solely to test
the logical strength of the analytic resonance component isolated by T29.

## Exact statement proved

There are a digit stream `d : N -> {0,...,9}`, a real number

```text
x = sum_(n >= 0) d_n 10^(-(n+1)),
```

and an explicit strictly increasing sequence of positive integers `(N_m)`
such that:

1. every finite decimal word occurs contiguously in `d`, including every word
   with one or more leading zeroes;
2. `d` is the canonical decimal expansion of `x` (it is neither eventually
   zero nor eventually nine);
3. for the single fixed nonzero frequency `h = 1`, if

   ```text
   S_N(x) = sum_(j=0)^(N-1) exp(2 pi i fract(10^j x)),
   ```

   then

   ```text
   lim_(m -> infinity) |S_(N_m)(x)| / N_m = 1.
   ```

In particular, the bare analytic fixed-frequency resonance conclusion of T29
does not by itself force failure of the generic V1/disjunctivity property for
an arbitrary decimal stream.

## Normalization and ambiguous quantifiers

The following choices make every relevant quantifier explicit.

1. A digit is an element of `D = {0,1,...,9}`.
2. A finite word is any finite list over `D`. The empty word is allowed and
   occurs vacuously at every position. A nonempty word may begin with any
   number of zeroes; words are not identified with integer representations.
3. An occurrence of `w = (w_0,...,w_(ell-1))` in `d` means that there is one
   `a in N` such that `d_(a+i) = w_i` for every `0 <= i < ell`.
4. `fract(t)` is the unique member of `[0,1)` differing from `t` by an
   integer.
5. The frequency is fixed once and for all as `h = 1`; it does not vary with
   `m` or with the prefix length.
6. The prefix lengths are the explicit recursively defined endpoints `N_m`
   below, not lengths selected after inspecting finite sums.
7. "Modulus tending to 1" means the normalized modulus
   `|S_(N_m)(x)| / N_m`, not merely an unnormalized lower bound.
8. "Non-pi" means that the constructed real is not pi and that this is not a
   claim about pi's digit stream. Indeed, the constructed `x` lies in
   `(0,1/10)`, whereas `pi > 3`.

The canonical V1/V2/V3 ambiguity is unchanged: V1 concerns finite contiguous
words in pi, V2 concerns infinite tails, and V3 concerns scattered infinite
subsequences. This note proves none of those pi statements.

## Pinned accepted inputs

Only the following accepted construction is reused.

| Input | Exact fact used | SHA-256 |
|---|---|---|
| `knowledge_library/t22/ChampernowneDisjunctive.lean` | `Theory.PiDigits.T22.champernowne_everyFiniteDecimalWord`: every finite list of `Fin 10`, including leading-zero lists, occurs in the Champernowne stream. The explicit leading-zero corollary is `champernowne_everyLeadingZeroWord`. | `a55a5eb9d2a59b9ab363d24c5bd25edf52166d9e804d2a92b9d08c58432a662d` |
| `knowledge_library/t29/FixedFrequencyResonance.lean` | The logical comparison only: T29's analytic component has one fixed nonzero frequency and unbounded resonant prefix lengths. No T29 theorem is used to prove the construction. | `36bccfb678a9e3452bb4321a518541d2d0c9af79b995e1305ae47bc35d11c171` |

No literature theorem and no computation over a finite prefix is used.

## Construction of the stream

Let `C = C_0 C_1 C_2 ...` be the decimal Champernowne digit stream

```text
1234567891011121314...
```

formalized in T22. For `m >= 1`, let

```text
P_m = C_0 C_1 ... C_(m-1)
```

be its prefix of exactly `m` digits.

We recursively define finite words `A_m` and four integer lengths. Start with

```text
A_0 = 0,                    N_0 = |A_0| = 1.
```

For each `m >= 1`, after `A_(m-1)` is defined, put

```text
B_m = N_(m-1) + m,
Z_m = m^2 B_m,
A_m = A_(m-1) P_m 0^(Z_m),
N_m = |A_m| = B_m + Z_m = (m^2 + 1) B_m.              (1)
```

Here `0^Z` denotes a word of exactly `Z` zeroes. Thus `B_m` is the endpoint
of the `m`th Champernowne island and `N_m` is the endpoint of its following
zero block. Every `A_(m-1)` is an initial segment of `A_m`, so there is a
unique infinite stream `d` having every `A_m` as an initial segment. In fully
expanded notation,

```text
d = 0 P_1 0^(Z_1) P_2 0^(Z_2) P_3 0^(Z_3) ... .       (2)
```

This definition is independent of any experimental values of the digits or
the exponential sums.

Equation (1) also proves that the selected prefixes are unbounded. Since
`B_m = N_(m-1)+m >= m`,

```text
N_m = (m^2+1)B_m >= (m^2+1)m >= m.                    (3)
```

Moreover `N_m > N_(m-1)`, because `N_m = N_(m-1) + m + Z_m` with
`m >= 1`. Hence `(N_m)_(m>=1)` is an explicit strictly increasing unbounded
sequence.

## Coverage of every finite word

Let `w = (w_0,...,w_(ell-1))` be an arbitrary finite decimal word. If
`ell = 0`, it occurs vacuously. Suppose `ell > 0`.

By T22's `champernowne_everyFiniteDecimalWord`, there is an index `a` such
that

```text
C_(a+i) = w_i             for every 0 <= i < ell.      (4)
```

Choose any `m >= a + ell`, for example `m = a + ell`. Then all positions in
(4) lie in `P_m`. In (2), `P_m` begins immediately after `A_(m-1)`, at global
position `N_(m-1)`. Therefore

```text
d_(N_(m-1) + a + i) = C_(a+i) = w_i
```

for every `0 <= i < ell`. Thus `w` occurs contiguously in `d`.

Nothing in this argument removes initial zeroes. In particular, for every
finite `v`, apply the same argument to the literal list `w = 0 :: v`.
T22's theorem covers that list by embedding it inside a suitable ordinary
integer block after a prefixed `1`; the occurrence copied into `P_m` retains
the leading zero. The same applies to words `00 :: v`, and inductively to any
number of leading zeroes. Hence `d` has the generic V1/disjunctivity property.

## Decimal-real encoding

Regard each `d_n` as an integer in `[0,9]` and define

```text
x = sum_(n=0)^infinity d_n 10^(-(n+1)).                (5)
```

The series converges absolutely because

```text
0 <= d_n 10^(-(n+1)) <= 9 * 10^(-(n+1))
```

and the upper geometric series sums to `1`. More sharply, `d_0 = 0`, so
`x <= 1/10`. Equality would require every digit after `d_0` to be `9`, but
already the first zero block supplies a positive deficit from that geometric
upper bound. Thus the inequality is strict. Also `x > 0` because every island
begins with `C_0 = 1`. Consequently

```text
0 < x < 1/10.                                             (6)
```

There are infinitely many zero digits: every stage adds a nonempty zero
block. There are also infinitely many nonzero digits: every later island
`P_m` starts with `C_0 = 1`. Thus (2) is neither eventually nine nor
eventually zero. It is therefore the canonical nonterminating decimal
expansion of (5), with no `0.999...` or terminating-expansion ambiguity.

For completeness, fix `j >= 0` and split (5) at `j`:

```text
10^j x = I_j + y_j,
I_j = sum_(n=0)^(j-1) d_n 10^(j-1-n) in Z,
y_j = sum_(r=0)^infinity d_(j+r) 10^(-(r+1)).            (7)
```

We have `0 <= y_j <= 1`. In fact `y_j < 1`: after every position `j` there is
a later zero block, so the tail contains a zero, whereas equality in the
geometric upper bound would require every digit of that tail to be `9`.
Hence (7) gives the exact tail identity

```text
fract(10^j x) = y_j = 0.d_j d_(j+1) d_(j+2) ... .        (8)
```

The floor-extracted digit is also explicit. Splitting off the first term gives

```text
y_j = d_j/10 + y_(j+1)/10,       0 <= y_(j+1) < 1,
```

and therefore

```text
d_j <= 10 y_j < d_j+1,           floor(10 y_j) = d_j.
```

Thus the canonical decimal digits of `x` are exactly the constructed `d_j`,
not merely a representation of the same real. This verifies directly that
the exponential sums below are attached to the stated decimal stream.

## Fixed-frequency phase estimate

Write

```text
e(t) = exp(2 pi i t),
S_N(x) = sum_(j=0)^(N-1) e(fract(10^j x)).                (9)
```

This is frequency `h = 1`, fixed independently of `m` and nonzero.

Consider `N = N_m`, the endpoint of the `m`th zero block. The first `B_m`
indices `0 <= j < B_m` precede that zero block. Among its `Z_m` positions,
call an index good if

```text
B_m <= j < N_m - m.                                      (10)
```

There are exactly `Z_m - m` good indices. This number is nonnegative because
`Z_m = m^2 B_m >= m`. At a good index, the next `m` digits
`d_j,...,d_(j+m-1)` are all zero. The tail formula (8) and the geometric
series then give

```text
0 <= fract(10^j x)
   <= sum_(r=m)^infinity 9 * 10^(-(r+1))
    = 10^(-m).                                            (11)
```

The endpoint `j = N_m-m` would also have `m` zero digits available. We omit
it deliberately, so (10) is a conservative half-open range and there is no
boundary off-by-one assumption in the estimate.

For real `t`, the elementary chord bound

```text
|exp(iu)-1| <= |u|
```

with `u = 2 pi t` gives

```text
|e(t)-1| <= 2 pi |t|.                                    (12)
```

Combining (11) and (12), each good index contributes at most
`2 pi 10^(-m)` to `|e(fract(10^j x))-1|`.

All remaining indices are treated without assumptions on their phases.
There are `B_m` indices before the zero block and `m` final indices in the
zero block, for a total of `B_m+m` bad indices. Since every complex
exponential has modulus one, each bad index satisfies

```text
|e(fract(10^j x))-1| <= 2.                               (13)
```

The triangle inequality, (11)-(13), and `Z_m-m <= N_m` now give the explicit
finite-prefix estimate

```text
sum_(j=0)^(N_m-1) |e(fract(10^j x))-1|
 <= 2(B_m+m) + (Z_m-m) 2 pi 10^(-m),

|S_(N_m)(x)/N_m - 1|
  = (1/N_m) |sum_(j=0)^(N_m-1) (e(fract(10^j x))-1)|
 <= 2(B_m+m)/N_m + 2 pi 10^(-m).                         (14)
```

No limiting assertion has yet been used in obtaining (14).

By (1), `B_m/N_m = 1/(m^2+1)`. Also `B_m >= m`, so

```text
m/N_m <= B_m/N_m = 1/(m^2+1).
```

Thus (14) yields the simpler fully explicit bound

```text
|S_(N_m)(x)/N_m - 1|
 <= 4/(m^2+1) + 2 pi 10^(-m).                            (15)
```

Both terms on the right tend to zero. Therefore

```text
S_(N_m)(x)/N_m -> 1.                                     (16)
```

The reverse triangle inequality gives

```text
abs(|S_(N_m)(x)|/N_m - 1)
 <= |S_(N_m)(x)/N_m - 1|,
```

so (15) proves the requested maximal subsequential resonance:

```text
lim_(m -> infinity) |S_(N_m)(x)|/N_m = 1.                (17)
```

The universal triangle inequality `|S_N(x)| <= N` shows that `1` is the
largest possible normalized modulus, hence "maximal" is literal.

## Exact comparison with T29's analytic quantifiers

T29 writes its pi sum with the raw phase rather than `fract`. For this
constructed `x`, the two conventions agree at every integer frequency `h`:

```text
exp(2 pi i h fract(10^j x)) = exp(2 pi i h 10^j x),       (18)
```

because `10^j x - fract(10^j x)` is an integer. Thus (17) is also a statement
about the raw-phase sum used by T29 after replacing pi by `x`.

The genericized analytic conjunct can be matched with T29's concrete
constants. Take

```text
k = 1,       H(1) = 2 * 10^2 = 200,
epsilon(1) = 1/(8 * 10^2) = 1/800,       h = 1.
```

Then `h != 0` and `|h| <= H(1)`. By (17), there is `M` such that for all
`m >= M`,

```text
|S_(N_m)(x)| / N_m >= 1/2 > 1/800.
```

Given any threshold `B`, choose `m >= max(M,B)`. Equation (3) gives
`N_m >= m >= B`, and hence

```text
epsilon(1) N_m <= |sum_(j=0)^(N_m-1) exp(2 pi i 10^j x)|. (19)
```

This has the exact order `exists h, forall B, exists N >= B`, with `h` fixed
before `B`. It is the generic `x` analogue of T29's bare analytic resonance
conclusion, and in fact (17) is substantially stronger.

## Logical conclusion and limitations

The stream `d` is disjunctive by (4), yet its fixed-frequency normalized
exponential sums have subsequential modulus tending to the maximum possible
value by (17). Consequently, an assertion consisting only of

```text
there exists one fixed h != 0 and unbounded prefix lengths along which
the normalized exponential sums stay bounded away from zero
```

is not sufficient to infer failure of the generic V1/disjunctivity property.
Indeed this example satisfies the much stronger conclusion that the
normalized modulus tends to `1` at `h = 1`.

This conclusion concerns only the **bare analytic resonance component** of
T29. T29 itself is a valid one-way implication from failure of canonical V1
for pi to resonance, and its displayed theorem also records an actually
missing word in its conclusion. The present disjunctive example has no
missing word and therefore does not satisfy that full package. It does not
refute T29, its contrapositive, or any theorem imported by T29.

Finally, this construction proves nothing about the decimal digits of pi,
proves neither canonical V1 nor its negation, and proves nothing about sibling
V3 or its negation. It only separates T29's necessary analytic obstruction
from a sufficient criterion for failure of disjunctivity in arbitrary
decimal streams.

## Experiments and formalization map

- Experiments: none. No finite-prefix values were computed or used.
- Lean statement: none claimed for T31; this artifact is a `proof sketch`.
- Reused machine-checked input: T22's Champernowne coverage theorem.
- Independent review: pending.
