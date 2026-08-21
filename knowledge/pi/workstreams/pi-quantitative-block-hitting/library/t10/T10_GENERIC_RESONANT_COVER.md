# T10: an explicit resonant decimal stream with uniform word deadlines

Status: `proof sketch`

## Provenance and scope

- Agenda item: T10, serving G9.
- Canonical source: `knowledge/pi/statements/pi-quantitative-block-hitting.txt`.
- Canonical source SHA-256:
  `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`.
- Original source URL: none; this is a locally formulated problem, and the
  canonical source records its provenance.
- Reused accepted artifact:
  `knowledge_library/t2/ChampernowneQuantitativeCover.lean`, SHA-256
  `08bc99f3aaea00d8db4197d1c1a4b00b1afcc51dde4e55d1a959f059c35d3c4e`.
  In particular, T2's public `finiteConcat_length_le_mul` is the generic
  finite-concatenation estimate underlying the fixed-length enumeration
  below. We use the simpler exact-length instance rather than reproduce T2's
  variable-length decimal encoding.
- Orbit-sum definition checked in
  `TheoryLib/PiDigits/T27FiniteExponentialCylinderCoverage.lean`, SHA-256
  `fd9c730e411dd7fb12b5b1a103c683238595c68bbea0f06af0250b4d13a8ee4e`.

This is a **sibling separation for an explicitly constructed stream**. It is
not a statement about the digits of pi, proves nothing about C1, and makes no
novelty claim. It shows only that bare frequency-one resonance, considered as
a property of an arbitrary decimal stream, does not imply failure of a
uniform quantitative word-cover bound. Thus there is no generic-stream-level
converse to T8 based on bare resonance alone. It does not rule out a converse
that uses additional pi-specific information.

## Normalized statement

Let `D = {0,1,...,9}`. There is an explicitly defined sequence
`d = (d_n)_(n >= 0)` in `D`, an integer

```text
C_sep = 13,
```

and a real constant

```text
rho = 1/3,
```

with the following properties.

1. For every integer `k >= 1` and every `w in D^k`, including words whose
   first digit is zero, there is a zero-based start `n >= 0` such that

   ```text
   n + k <= C_sep * k * 10^k
   ```

   and `d_(n+r) = w_r` for every `0 <= r < k`. Thus the occurrence is
   contiguous and fully contained in the indicated prefix.
2. Define the real represented by the stream and its base-10 orbit by

   ```text
   x   = sum_(r=0)^infinity d_r * 10^(-(r+1)),
   y_n = fract(10^n * x).
   ```

   There is an explicit strictly increasing sequence `N_k`, `k >= 1`, such
   that

   ```text
   |sum_(n=0)^(N_k-1) exp(2*pi*i*y_n)| / N_k >= rho.
   ```

The phase convention is exactly T27's frequency-one phase
`Theory.PiDigits.T27.phase 1 y_n`, and the unnormalized sum is T27's
`exponentialSum y N_k 1`.

## Quantifier and convention audit

- `C_sep` is one constant independent of `k` and `w`.
- The assertion is for every `k >= 1`, not merely sufficiently large `k`.
- The enumeration is over all `10^k` words, so leading-zero words are not
  excluded.
- Starts are zero-based. The canonical one-based start is `i = n+1`, and
  `i+k-1 = n+k`, so the displayed inequality is exactly full containment.
- The endpoint sequence is indexed by every `k >= 1`, is strictly increasing,
  and hence supplies infinitely many unbounded endpoints.
- "Explicit generic stream" here means an explicit artificial stream in the
  class of decimal streams. It does not mean the digits of a topologically
  generic, measure-generic, or named mathematical constant.

## Stream definition

For `k >= 1` and `0 <= q < 10^k`, let `w(k,q)` be the length-`k` base-10
expansion of `q`, padded on the left with zeros. Explicitly, for
`0 <= r < k`,

```text
w(k,q)_r = floor(q / 10^(k-1-r)) mod 10.
```

Let `E_k` be the concatenation in increasing order of `q`:

```text
E_k = w(k,0) w(k,1) ... w(k,10^k-1).
```

Let `Z_k` be a block of exactly `100*k*10^k` zero digits, and let stage `k`
be

```text
A_k = E_k Z_k.
```

Finally, define `d` to be the infinite concatenation

```text
d = A_1 A_2 A_3 ... .
```

All components are finite and nonempty, so this specifies exactly one digit
at each zero-based position. Put

```text
a_k = k*10^k,
L_k = |Z_k| = 100*a_k,
N_0 = 0,
N_k = sum_(j=1)^k 101*j*10^j.
```

Since `|E_k| = a_k` and `|A_k| = 101*a_k`, `N_k` is exactly the exclusive
right endpoint of `Z_k`, not merely an upper bound for it.

## Lemma 1: exact word enumeration

For fixed `k`, the map `q -> w(k,q)` is the usual bijection from
`{0,...,10^k-1}` to `D^k`. Indeed, positional expansion gives

```text
q = sum_(r=0)^(k-1) w(k,q)_r * 10^(k-1-r),
```

and conversely the right side maps an arbitrary `w in D^k` to an integer in
`[0,10^k)`, whose padded expansion is `w`. This includes, for example, the
all-zero word at `q=0` and every word beginning with zero.

Each listed block has length exactly `k`. Hence

```text
|E_k| = k*10^k = a_k,
```

and `w(k,q)` occupies the half-open interval

```text
[N_(k-1) + q*k, N_(k-1) + (q+1)*k)
```

of the full stream. This is the exact fixed-length instance of T2's finite
word-enumeration/concatenation machinery.

## Lemma 2: the all-k full-containment deadline

Fix `k >= 1` and `w in D^k`, and choose its unique index `q` from Lemma 1.
Its occurrence has start `n = N_(k-1)+q*k`, so

```text
n+k <= N_(k-1) + k*10^k.                       (1)
```

It remains to bound all earlier enumeration blocks and zero slabs. Since
`j <= k` for `1 <= j < k`, the finite geometric sum gives

```text
N_(k-1)
  = 101 * sum_(j=1)^(k-1) j*10^j
  <= 101*k * sum_(j=1)^(k-1) 10^j
  = 101*k*(10^k-10)/9.
```

There is no asymptotic step here. Clearing the positive denominator `9`
and adding the current enumeration block gives

```text
9*(N_(k-1) + k*10^k)
  <= 101*k*(10^k-10) + 9*k*10^k
   = 110*k*10^k - 1010*k
  <= 110*k*10^k
  <= 117*k*10^k
   = 9*(13*k*10^k).
```

Together with (1), division by `9` proves

```text
n+k <= 13*k*10^k.
```

This proof holds for every `k >= 1`; when `k=1`, the empty earlier-stage sum
is zero and the same inequalities remain valid.

## Lemma 3: endpoint growth and zero-slab proportion

The endpoints are strictly increasing because

```text
N_(k+1)-N_k = 101*(k+1)*10^(k+1) > 0.
```

Also `N_k >= 101*k*10^k >= k`, so `(N_k)` is unbounded.

For the proportion estimate, use `j <= k` for `1 <= j <= k`:

```text
N_k
  = 101 * sum_(j=1)^k j*10^j
  <= 101*k * sum_(j=1)^k 10^j
  = 101*k*(10^(k+1)-10)/9
  <= (1010/9)*a_k.
```

Because `L_k=100*a_k`, clearing denominators verifies the convenient exact
form

```text
8*N_k <= 9*L_k.                                 (2)
```

For completeness, multiply the preceding bound by `72` rather than divide:

```text
72*N_k <= 8080*a_k <= 8100*a_k = 81*L_k,
```

and divide by `9`. The numerical slack is `20*a_k` before that division.

## Lemma 4: orbit tails on a zero slab

The stream contains infinitely many zero slabs, so no suffix consists only
of nines. Consequently its displayed decimal expansion is not an
eventually-nine expansion. Splitting the defining series for `x` after `n`
digits therefore gives the exact tail identity

```text
y_n = fract(10^n*x)
    = sum_(r=0)^infinity d_(n+r)*10^(-(r+1)),    (3)
```

with `0 <= y_n < 1`.

If `n` lies in the current slab `Z_k`, then `d_n=0`. Bounding every later
digit by `9` in (3) gives

```text
0 <= y_n
  <= 9 * sum_(r=1)^infinity 10^(-(r+1))
   = 1/10.                                       (4)
```

Thus `0 <= 2*pi*y_n <= pi/5 < pi/3`. Cosine is decreasing on `[0,pi]`, so

```text
Re(exp(2*pi*i*y_n)) = cos(2*pi*y_n) >= cos(pi/3) = 1/2.   (5)
```

For every other `n`, the universal bound `cos(2*pi*y_n) >= -1` applies.

## Theorem: fixed-frequency resonance at every stage endpoint

Let

```text
S_k = sum_(n=0)^(N_k-1) exp(2*pi*i*y_n).
```

Exactly `L_k` indices in this prefix belong to the current zero slab `Z_k`.
Using (5) on those indices and `Re(exp(...)) >= -1` on all remaining indices,

```text
Re(S_k)
  >= (1/2)*L_k - (N_k-L_k)
   = (3/2)*L_k - N_k.                            (6)
```

Estimate (2) says `L_k >= (8/9)*N_k`. Substitution in (6) yields

```text
Re(S_k)
  >= (3/2)*(8/9)*N_k - N_k
   = (1/3)*N_k.
```

Since the complex norm dominates the real part,

```text
|S_k| / N_k >= 1/3 = rho                         (7)
```

for every `k >= 1`. In particular, (7) holds at infinitely many explicitly
defined unbounded endpoints. The frequency is the fixed integer `h=1`; it
does not vary with `k`.

## Conclusion and non-transfer warning

The explicit stream `d` simultaneously satisfies the all-length
full-containment bound with `C_sep=13` and the frequency-one normalized
orbit-sum lower bound with `rho=1/3` along `(N_k)`. Long zero slabs therefore
do not quantitatively conflict with `O(k*10^k)` word deadlines: geometric
growth leaves enough room for both.

This establishes only the requested sibling separation. The constructed real
is not pi, no property of pi was used, and no transfer theorem from this
stream to pi is asserted. Hence the canonical C1 question remains open.
