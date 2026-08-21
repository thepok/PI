# T18: T13 resonance versus the irrationality measure of pi

Status: `proof sketch` with a source-pinned irrationality theorem.

Verdict: **INSUFFICIENT**.  The accepted T13 theorem yields special rational
approximations to pi, but its guaranteed error has exponent tending to 1 when
expressed in terms of the available denominator bound.  This is compatible
with the published upper bound `7.103205334137...` for the irrationality
measure of pi.  No conclusion below proves canonical A1.

## 0. Immutable statement and scope

The canonical statement is
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`, SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It defines the ordered, diagonal-inclusive count `Q_pi(n,N)` and asks for

```text
forall A >= 1, exists n0 >= 1, forall n >= n0, exists N >= 1,
    A*n*Q_pi(n,N) <= N^2.                              (A1)
```

T18 tests the literal negation of this exact A1.  It does not replace the
eventual quantifier by an infinitely-often quantifier, prescribe `N`, remove
the diagonal, or change strict circle distance.  Those are the statement's
recorded sibling readings A2--A16, not the claim considered here.

The accepted input is
`knowledge_library/t13/IteratedLagResonance.lean`, SHA-256

```text
14ae452f34068dd78877054e231c58af02c2563cd755f0ee4edc0ff0ebeeda13.
```

Exact locators in that file are: definitions of the density loss and length
thresholds at lines 28--51; the resonance sum at lines 64--69; and
`literal_not_A1_implies_arbitrary_depth_resonance` at lines 629--702.  T13 is
`machine-checked`; the deductions in this note are not Lean formalizations.

## 1. Literal T13 specialization and quantifier dependencies

Assume the literal negation of A1:

```text
not (forall A : N, 1 <= A -> exists n0 : N, 1 <= n0 and
     forall n : N, n0 <= n -> exists N : N, 1 <= N and
     A*n*Q_pi(n,N) <= N^2).                            (1)
```

T13 gives an integer `A >= 1` such that, for every `n0 >= 1`, there is an
integer `n >= n0` with `n >= 1` such that the following holds for every depth
`d >= 0` and every requested residual length `K >= 1`.  There are integers
`N,r,h` and an injective family of shifts `(s_t)_(t in Fin d)` satisfying

```text
D0 := 131072*A^2*n^2 = 2^17*A^2*n^2,
T_d(K) := iterationLengthThresholdAux(D0,1,K,1,d),
N = 16*A*n*T_d(K),                                    (2)
1 <= r <= N-1,
1 <= h <= H := 256*A*n,
1 <= s_t,  s_t != r,  and the s_t are pairwise distinct,
L := N-r-sum_t s_t >= K,                              (3)
|sum_(0 <= j < L) e(10^j*a*pi)| > L/D_d,              (4)
a := h*(10^r-1)*prod_t(10^(s_t)-1),
e(x) := exp(2*pi*i*x),
D_d := densityDenominator(D0,d).
```

The dependency order matters:

```text
exists A, forall n0, exists n, forall d, forall K, exists witnesses.
```

Thus `A,n` are fixed before `d,K`; all of `N,r,h,s_t,a,L` may change with
`K`.  T13 does not provide a coherent witness sequence as `K` grows.

There is a potentially confusing normalization in (4).  T13's
`geometricPhase c j` is `exp(2*pi*i*10^j*c)`, and here `c=a*pi`.  Therefore
the circle coordinate is `a*pi`, so differencing gives near-integers of
integer multiples of pi.  Expanding the complex exponent produces
`2*i*10^j*a*pi^2`, but it would be wrong to infer that the circle coordinate
is `a*pi^2` or that T13 directly approximates `pi^2`.

## 2. Exact density loss and differencing depth

Put `D_i := densityDenominator(D0,i)`.  The T13 recursion is

```text
D_(i+1) = 8*D_i^2.
```

Induction gives, for every `i >= 0`,

```text
D_i = 8^(2^i-1)*D0^(2^i)
    = 2^(20*2^i-3)*(A*n)^(2^(i+1)).                   (5)
```

In particular the density retained after depth `d` is `1/D_d`; the loss is
doubly exponential in `d`.

The length recursion can also be written without `max`.  At stage `i`, the
forbidden-shift count is `i+1`, the lower shift bound is 1, and the remaining
threshold is at least `K >= 1`.  Hence the second term

```text
16*(1+(i+1)+R)*D_i^2
```

is at least `48*D_i^2` and strictly dominates `8*D_i^2`.  Define

```text
lambda_i := 16*D_i^2,
C_d := prod_(0 <= i < d) lambda_i
     = 2^(40*(2^d-1)-2*d)*(A*n)^(4*(2^d-1)),          (6)
E_d := sum_(0 <= i < d) (i+2)*prod_(0 <= v <= i) lambda_v.
```

Empty products and sums give `C_0=1`, `E_0=0`.  Unrolling the recursion gives
the exact affine formula

```text
T_d(K) = C_d*K + E_d.                                 (7)
```

Since `K <= L` and `L >= 1`, (2) and (7) imply

```text
N <= Gamma_d*L,
Gamma_d := 16*A*n*(C_d+E_d).                          (8)
```

Equations (5)--(8) explicitly account for density loss, differencing depth,
the requested residual length, and the resulting ambient length.

## 3. Coefficient growth and harmonic cutoff

Because `L >= K >= 1`, the natural-number subtractions in (3) do not truncate;
thus

```text
r + sum_t s_t + L = N.                                (9)
```

All factors defining `a` are positive integers.  Using the harmonic cutoff
`h <= H=256*A*n`, (9), and `10^u-1 < 10^u` for `u>=1`,

```text
1 <= a < H*10^(r+sum_t s_t) = H*10^(N-L).             (10)
```

The `d+1` integers `r,s_0,...,s_(d-1)` are distinct and positive.  Therefore

```text
a >= prod_(u=1)^(d+1) (10^u-1).                       (11)
```

This lower bound will let us put every eventual approximation beyond the
existential denominator threshold in the cited irrationality theorem.

## 4. What the resonance magnitude itself proves

Take `K>=2`, so `L>=2`, and write `z_j=e(10^j*a*pi)` and `S=sum_j z_j`.
Squaring (4) and expanding exactly gives

```text
|S|^2 = L + 2*sum_(0 <= j < k < L)
                  cos(2*pi*(10^k-10^j)*a*pi)
       > L^2/D_d^2.                                   (12)
```

There are `L*(L-1)/2` pairs.  Consequently at least one pair `j<k` has

```text
cos(2*pi*(10^k-10^j)*a*pi) > c_(L,d),
c_(L,d) := (L/D_d^2-1)/(L-1).                         (13)
```

Indeed, if every cosine were at most this value, the right side of the exact
identity in (12) would be at most `L^2/D_d^2`, a contradiction.  Since
`-1 <= c_(L,d) <= 1`, (13) gives the checkable near-integer statement

```text
||(10^k-10^j)*a*pi||_(R/Z)
    < arccos(c_(L,d))/(2*pi).                          (14)
```

If `L>D_d^2`, this is strictly less than `1/4`.  As `L` tends to infinity
with fixed `d`, however, the right side tends to
`arccos(D_d^(-2))/(2*pi)`, a positive constant close to `1/4`.  Thus the
accepted resonance magnitude alone supplies no shrinking error through this
pair-energy argument.

For a radical-free check, `1-cos(2*pi*x) >= 8*||x||_(R/Z)^2` follows from
`sin(pi*y)>=2y` on `0<=y<=1/2`; (13) therefore also gives

```text
||(10^k-10^j)*a*pi||_(R/Z)^2 < (1-c_(L,d))/8.          (15)
```

## 5. Sharp circular-pigeonhole consequence without a new inverse theorem

Apply circular pigeonhole to the `L+1` points consisting of 0 and
`10^j*a*pi (mod 1)`, `0<=j<L`.  The least circular gap between adjacent
points is at most `1/(L+1)`.  Hence either some `0<=j<L` satisfies

```text
||10^j*a*pi||_(R/Z) <= 1/(L+1),
```

or some `0<=j<k<L` satisfies

```text
||(10^k-10^j)*a*pi||_(R/Z) <= 1/(L+1).                (16)
```

This is the sharp circular-pigeonhole estimate used in this note.  It is
important that (16) uses the orbit and residual length supplied by T13 but
**does not use the lower bound (4)**: it holds for arbitrary circle points.
Treating (16) as a resonance inverse theorem would be an overstatement.

In the first case set `q:=a*10^j`; in the second set
`q:=a*(10^k-10^j)`.  In either case `q>=1`, and by the definition of circle
distance there is `p in Z` with

```text
|q*pi-p| <= 1/(L+1),
|pi-p/q| <= 1/(q*(L+1)) <= 1/(q*K).                   (17)
```

The special denominator in (17) has the explicit bounds

```text
prod_(u=1)^(d+1)(10^u-1) <= q                         (18)
q < H*10^(N-L)*10^(L-1) = H*10^(N-1)
  < H*10^(Gamma_d*L).                                 (19)
```

For (18), the extra factor is either `10^j` or `10^k-10^j` and is at least
1.  For (19), that factor is at most `10^(L-1)`; the strict inequality follows
from the strict coefficient bound (10), and the last inequality uses (8).
This tracks all coefficient growth available from T13.  Crucially, (19) is
exponential, not polynomial, in `L`.

## 6. Source-pinned irrationality theorem

The retained source is Doron Zeilberger and Wadim Zudilin, *The irrationality
measure of pi is at most 7.103205334137...*, Moscow Journal of Combinatorics
and Number Theory 9 (2020), no. 4, 407--419,
DOI `10.2140/moscow.2020.9.407`.  Full URLs, hashes, and locators are in
`SOURCE_PINS.md`.

On printed p. 407 (PDF page 2), lines 27--34 of the retained layout extract,
the paper defines the irrationality measure `mu(x)` by the quantifiers

```text
for every epsilon>0, for all integers p and all sufficiently large
integer q: |x-p/q| > q^(-(mu+epsilon)).                (20)
```

On printed p. 418 (PDF page 13), the `World record` paragraph concludes from
Propositions 7 and 8 that

```text
mu(pi) <= M := 7.10320533413700172750577342281... .    (21)
```

Proposition 7 is on printed p. 417, extract lines 630--633; Proposition 8 and
its exact cubic are on printed p. 417, extract lines 635--646; and the final
calculation is at extract lines 676--691.  We need only the clean consequence
of (20)--(21) at exponent 8:

```text
exists Q8>=1, forall integers q>=Q8, forall p in Z,
    |pi-p/q| > q^(-8).                                (22)
```

The paper does not print a numerical value of `Q8`; (22) is an eventual
statement with an existential threshold.  No explicit threshold is asserted
here.

## 7. Final exponent comparison

The lower bound in (18) tends to infinity with `d`.  After `A,n` have been
selected by T13, choose a depth `d` so large that

```text
prod_(u=1)^(d+1)(10^u-1) >= Q8.                       (23)
```

This is permitted because T13 quantifies over every `d` after choosing `n`.
For this fixed depth and every `K>=2`, the denominator produced in Step 5 is
at least `Q8`.  Combining (17) and (22) gives

```text
q^(-8) < |pi-p/q| <= 1/(q*(L+1)),
therefore L+1 < q^7.                                  (24)
```

There is no contradiction.  T13 supplies only the exponential upper bound

```text
q < H*10^(Gamma_d*L),                                 (25)
```

and `(L+1)^(1/7) < H*10^(Gamma_d*L)` for every `L>=2`, since
`H,Gamma_d>=1`.  Thus the required lower growth `q>(L+1)^(1/7)` in (24) fits
far below the allowed exponential growth in (25).

For a denominator-form comparison, when `q>H`, (25) yields

```text
L > log(q/H)/(Gamma_d*log 10),
|pi-p/q| < Gamma_d*log(10)/(q*log(q/H)).               (26)
```

The guaranteed approximation exponent represented by the right side of (26)
tends to 1, not to a number exceeding `M`.

More generally, a hypothetical missing bound `q <= c*L^C` would turn (17)
into

```text
|pi-p/q| <= c^(1/C)*q^(-(1+1/C)).                     (27)
```

For arbitrarily large `q`, this could conflict with (21) only if

```text
1+1/C > M,
equivalently C < 1/(M-1) = 0.163848329730397... .      (28)
```

T13 proves no polynomial bound at all, let alone the sublinear power required
by (28).  Equations (24)--(28) are the final exponent comparison.

## 8. Isolated gaps and verdict

**INSUFFICIENT.**  Known irrationality measures do not contradict the accepted
T13 obstruction with its present quantitative data.  Closing this route would
require at least one new, presently unproved statement:

1. A resonance inverse theorem that uses (4), rather than bare pigeonhole, to
   produce near-integer error much smaller than `1/L`.
2. A coefficient-growth theorem relating the resulting denominator to `L` by
   `q <= c*L^C` with `C<0.163848329730397...`, or another estimate that beats
   exponent `M`.
3. Cross-`K` coherence or direct witness control strong enough to prevent the
   lags and shifts from making `q` exponentially large.

None of these statements is used as a theorem in this note.  In particular,
the large exponential sum is not silently converted into a small linear form,
and the existential threshold in the irrationality source is not made
numerical.  Consequently this note neither proves A1 nor proves the premise
`not A1`; it only shows that T13's accepted necessary obstruction is
quantitatively compatible with the cited irrationality measure.
