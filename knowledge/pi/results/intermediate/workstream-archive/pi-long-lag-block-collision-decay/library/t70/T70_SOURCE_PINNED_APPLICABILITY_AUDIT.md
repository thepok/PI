# T70 source-pinned applicability audit

Audit date: 2026-08-03 UTC

Claim label: `literature-checked` applies only to the source statements,
locators, and applicability comparisons recorded here. No fixed-`pi`
aggregate or discrepancy estimate is proved. In particular, this note does not
assert T69's premise, T29, C1, C2, or C3.

## 1. Scope and immutable statement

`CANONICAL_STATEMENT.txt` is the byte-exact local statement, SHA-256

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

The problem was formulated locally and has no external source URL. Lines 1-10
ask the canonical ordered all-`m,N` question with quantifiers
`forall s, exists C_s, forall positive m,N`. T70 does not answer it. The
audited target is the distinct residual-A12, `m = 1`, dyadic primitive-sector
interface in the kernel-checked T69 module. This sibling status is not changed
anywhere below.

The recorded quantifier ambiguities relevant here are:

- a constant depending on `t` is insufficient;
- an eventual estimate with an onset depending on a newly introduced shift is
  insufficient without a uniform-on-shifts argument;
- an almost-everywhere phase does not include the prescribed phase `pi`;
- an average over the phase or arc center is not a pointwise supremum;
- separate estimates in `(h,r)` need not retain pooled cancellation.

## 2. Imported kernel-checked T69 interface

The retained byte-exact source is `T69_KERNEL_INTERFACE.lean`, SHA-256

```text
09086eff08c0c09eefe02979107026fb3f19019887767b72d582ea0580e18301
```

It is copied from the accepted kernel-checked T69 library entry. T70 imports
its established conditional interface; it does not reprove or strengthen it.
Exact source locators are:

- lines 30-59: `aggregateEnergy`, `AggregateShiftedCorrelation`, and the
  literal aggregate identity;
- lines 63-128: summed van der Corput and constant `9/4`;
- lines 130-159: pooled count, exact mass, pooled excess, and shifted sum;
- lines 243-275: exact total mass and `CombinedHalfArcDiscrepancy`;
- lines 330-424: Fourier identity and `10 + 2*pi*Delta` implication;
- lines 446-492: failure certificate and T68 constant
  `10*(1 + pi*Delta)`;
- lines 494-610: exact T63 polynomial and primitive-budget constants;
- lines 612-880: fully literal theorem statements.

### 2.1 Literal aggregate target

For every natural `t`, define

```text
N_t = 4*2^t + 1,
H_t = ceil(sqrt(N_t)),
e(x) = exp(2*pi*i*x).
```

The first `pi` in `e` is the circle normalization. The phase below is the
second, prescribed real number `pi`. Put

```text
A_t = sum_{h=1}^{10} sum_{r=1}^{H_t-1} (H_t-r)
        sum_{k=0}^{N_t-r-1} e(h*(10^r-1)*10^k*pi).
```

Thus the integer frequency is exactly

```text
h*(10^r-1)*10^k = h*(10^(k+r)-10^k).
```

T69's literal identity is

```text
aggregateEnergy(t) = 10*H_t*N_t + 2*Re(A_t).
```

Its premise is exactly

```text
there exists a real K with 0 <= K such that, for every natural t,
  10*H_t*N_t + 2*Re(A_t) <= K*H_t*N_t.              (AGG)
```

The order is `exists K, forall t`; no witness is supplied at `pi`. A stronger
sufficient estimate

```text
there exists C >= 0 such that, for every t,
  |A_t| <= C*H_t*N_t
```

would give `(AGG)` with `K = 10 + 2*C`. The narrower one-sided estimate
`Re(A_t) <= C*H_t*N_t` gives the same constant and is all that T69 needs.

### 2.2 Literal pooled half-arc target

Represent the circle in `[-1/2,1/2)` and use the half-open centered half-arc
`[-1/4,1/4)`. For an arc center `y`, let

```text
P_t(y) = sum_{h=1}^{10} sum_{r=1}^{H_t-1} (H_t-r) *
  (#{0 <= k < N_t-r :
       centeredRepresentative(h*(10^r-1)*10^k*pi - y)
         is in [-1/4,1/4)} - (N_t-r)/2).
```

Multiplicity is retained. T69's exact total pre-arc mass is

```text
M_t = 10*H_t*(H_t-1)*(3*N_t-H_t-1)/6.
```

The combined discrepancy premise is exactly

```text
there exists Delta >= 0 such that, for every natural t and every y,
  |P_t(y)| <= Delta*H_t*N_t.                          (DISC)
```

T69 proves `(DISC) -> (AGG)` with

```text
K = 10 + 2*pi*Delta.
```

It also proves that failure of every aggregate constant forces, for every
`Delta > 0`, one scale and one explicitly oriented half-open half-arc with
positive pooled excess greater than `Delta*H_t*N_t`. Endpoint conventions are
therefore not disposable null-set conventions in that pointwise certificate.

### 2.3 Downstream constants, still conditional

Under `(AGG)`, T69 gives

```text
sum_{h=1}^{10} X_h(N_t)^2 <= (9/4)*K^2*N_t^3.
```

Its selected-plus-defect numerator remains literally

```text
sum_h X_h(N_t)^2 - 4*(N_t-1)*sum_h X_h(N_t)
  + 20*N_t^2 - 30*N_t,
```

divided by `sqrt(N_t^2-1)`. For `0 < s < 1`, its specialized conditional
primitive-sector budget has the constant

```text
10*((45/16)*K^2 + 5) * (N_t + N_t^2*10^(-s)).
```

T68's stronger separate-shift discrepancy condition implies the aggregate
condition with `K = 10*(1 + pi*Delta)`. None of these implications asserts an
analytic premise at `pi`.

## 3. Non-duplication boundary

The unchanged T5 and T21 audits are referenced, not copied:

```text
knowledge_library/t5/APPLICABILITY_MATRIX.md
SHA-256 ab5bcb0ebd5eb590c849cc6620d4bdd764415ef9de88f2881d8ce48429715406

knowledge_library/t5/SOURCE_MANIFEST.md
SHA-256 ace2233019ea2a24e8b83fb49b03c968ca4f5a1f6d87e04327f12a784c70fc65

knowledge_library/t21/T21_APPLICABILITY_AUDIT.md
SHA-256 b468e509c4aa3b8bad7d833458578f94b4a5f0d95c53567a69a69e1598c525ae

knowledge_library/t21/SOURCE_MANIFEST.md
SHA-256 b1efc07b51c3904aa8aae3ef148e58fb5bd62a727651b7498c7e3ce43c88bcf8
```

T5 rows M1-M7 already cover Bailey--Crandall, Philipp, Fukuyama,
Rudnick--Zaharescu, Chernov--Kleinbock, and Rousseau. T21 covers
Demeter--Silva, Aistleitner--Berkes--Seip, and
Chang--Kerr--Shparlinski. Their rows and PDFs are not duplicated here.

## 4. Verdict convention

- `APPLIES`: the cited theorem supplies `(AGG)` or `(DISC)` with every source
  hypothesis discharged and one constant before all `t`.
- `CONDITIONAL`: one precisely named additional premise, together with the
  cited theorem, supplies the literal target with tracked constants.
- `DOES NOT APPLY`: a fixed-point, averaging, exceptional-set, support, range,
  or constant mismatch remains.

All verdicts concern the theorem as printed in the pinned source. No metric
theorem is evaluated at `pi`.

## 5. Applicability matrix

| ID | Retained theorem | Verdict | Fixed point and averaging | Literal range/support | Constants | Exact mismatch |
|---|---|---|---|---|---|---|
| D3 | Aistleitner--Fukuyama, Theorem 4, exact averaged interval identity | **DOES NOT APPLY** | Exact `L2(dx da)` identity, so both the phase `x` and arc origin `a` are averaged; no exceptional set, but no point evaluation | Applies separately to each `(h,r)` because its `10^k` frequencies are distinct; pooling all triples introduces multiplicities, and triangle inequality does not recover cross-channel cancellation | At half length the exact second moment is `L/4`; the pooled bound below is explicitly at most `5*H_t*N_t` | Correct average scale but neither `x=pi` nor `sup_y`; closed/half-open endpoints agree only under integration |
| D4 | Technau--Zafeiropoulos, Theorem 1 and Corollary 3, discrepancy under Fourier-decaying measures | **DOES NOT APPLY** | `mu`-almost every phase; Corollary 3 gives Fourier dimension zero for a particular failure set, not membership of `pi` in the good set | For each fixed `(h,r)`, `n_k=h(10^r-1)10^k` has ratio 10; every new multiplier can have its own onset | LIL upper constant at `q=10` is at most `166+664/(sqrt(10)-1)`; summing separate errors adds `sqrt(log log N_t)` beyond the target scale | Fixed `pi`, uniform onset over growing shifts, and pooled cancellation are absent |
| B1 | Bombieri--Iwaniec, Lemma 2.4, double large sieve | **DOES NOT APPLY** | Deterministic real bilinear inequality; it can retain the literal point `pi` and has no exceptional set | A rectangularized T69 sum fits `x=h(10^r-1)`, `y=pi*10^k`; the omitted triangular tail is only `O(H_t*N_t)` | Exact factor `(2*pi^2)^K product(1+X_jY_j)`; here `K=1`, `Y=1`, and `X` must be about `10^H_t` | Even ideal diagonal-only local energy leaves a `10^(H_t/2)` loss; source inequality cannot certify `O(H_t*N_t)` |
| B2 | Garaev, Theorem 1, double exponential sums modulo a prime | **DOES NOT APPLY** | Deterministic at rational additive characters `e_p`, not the real phase `pi` | Both outer multipliers and exponents must be consecutive intervals; `h(10^r-1)` is sparse, and useful ranges are polynomial in `p` | Four explicit terms in `Delta`, with `p^(o(1))`; nontrivial example starts near interval lengths `p^(2/7+epsilon)` | Rational transfer requires an exponentially large modulus, where T69 lengths are `p^(o(1))` and every saving is trivial |
| B3 | Kerr, Theorem 2, incomplete geometric sums modulo a prime | **DOES NOT APPLY** | Deterministic and uniform over nonzero finite-field multipliers, but only at `a/p` | A single `(h,r)` has the exact geometric form with `g=10`; source also requires length at most the order of 10 modulo `p` | Bounds contain `p^(1/8)` or `p^(1/4)`, powers `71/96`, `73/96`, `49/96`, and an order factor | The modulus needed to transfer `pi` makes the `p` factor exponential; suitable multiplicative order along such approximants is also unknown |
| L1 | Baker--Munsch--Shparlinski, Theorem 1.1, additive-energy sparse-modulus large sieve | **DOES NOT APPLY** | Squares are averaged over `j <= Q` and every reduced residue modulo `m_j`; no fixed irrational point | Requires `m_j=j^(alpha+o(1))`, `Q^alpha <= N <= Q^(2alpha)`, and a consecutive coefficient interval; `10^r-1` is exponential and `10^k` is sparse | Bound depends explicitly on ordinary and asymmetric additive energies and has a `Q^(o(1))` factor | Wrong averaging variable, growth class, support, and phase |

No retained row is `APPLIES` or `CONDITIONAL`.

## 6. Source comparisons

### 6.1 D3: exact averaged half-arc scale

Theorem 4 of Aistleitner--Fukuyama states that for distinct positive integers
`n_1,...,n_L` and `0 < z < 1`, the centered period-one indicator satisfies

```text
integral_0^1 integral_0^1
  (sum_{k=1}^L I_[a,a+z](n_k*x))^2 dx da = z*(1-z)*L.
```

For one fixed T69 pair `(h,r)`, take

```text
n_k = h*(10^r-1)*10^k,  0 <= k < N_t-r,  z=1/2.
```

These integers are distinct, so the exact squared `L2(dx da)` norm is
`(N_t-r)/4`. Minkowski gives the fully weighted comparison

```text
||P_t(alpha,a)||_L2(d alpha d a)
  <= (1/2) * sum_{h=1}^{10} sum_{r=1}^{H_t-1}
       (H_t-r)*sqrt(N_t-r)
  <= 5*H_t*(H_t-1)*sqrt(N_t)
  < 5*H_t*N_t.
```

The last inequality uses `H_t-1 < sqrt(N_t)`, which follows literally from
`H_t=ceil(sqrt(N_t))`. This is the closest positive scale match found. It
still does not bound the trace at
`alpha=pi`, and an `L2` norm in `a` does not bound every arc center. The source
uses centered periodized closed-interval indicators. Changing to half-open
intervals preserves its double integral because endpoints form a null set,
but it does not preserve a literal pointwise endpoint assertion.

### 6.2 D4: discrepancy remains metric and separately summed

Technau--Zafeiropoulos assumes a Hadamard gap `n_(k+1)/n_k >= q>1` and a
probability measure with Fourier decay `|mu_hat(t)| << |t|^(-eta)`. Theorem 1
then gives, for `mu`-almost every `x`,

```text
1/4 <= limsup N*D_N(n_k*x)/sqrt(N*log(log N)) <= C_q,
C_q <= 166 + 664/(sqrt(q)-1).
```

The T69 sequence for each fixed `(h,r)` has `q=10`. The source therefore
controls every interval only for almost every phase, with an onset that may
depend on that phase and sequence. Corollary 3 says that the set where the
normalized limsup is `0` or infinity has Fourier dimension zero. It does not
show that `pi` avoids the full exceptional set.

Even an illicit pointwise substitution followed by triangle inequality would
give separate-channel error of order

```text
sum_{h,r} (H_t-r)*sqrt((N_t-r)*log(log(N_t-r))),
```

which is of order `H_t*N_t*sqrt(log(log N_t))`, not a constant times
`H_t*N_t`. Thus fixed-point membership alone would not recover the pooled
cancellation T69 permits.

### 6.3 B1: fixed point retained, but the range factor is terminal

Bombieri--Iwaniec Lemma 2.4 is a deterministic double large sieve. In one
dimension it bounds the square of a bilinear form by

```text
2*pi^2*(1+X*Y) * B(b;X) * B(a;Y),
```

where the two `B` factors are local pair energies at spacings `1/(2X)` and
`1/(2Y)`. If the `x` coordinates are integers, journal page 454 permits circle
distance in the `y` coordinate and sets `Y=1`.

First replace every `k < N_t-r` by `k < N_t`. The absolute tail is exactly at
most

```text
10*sum_{r=1}^{H_t-1} (H_t-r)*r
  = (10/6)*(H_t^3-H_t).
```

Since `N_t >= 5` and `H_t=ceil(sqrt(N_t))`, `H_t^2 <= 2*N_t`, so this is at
most `(10/3)*H_t*N_t`. Rectangularization therefore costs only an admissible
constant.

For the rectangular sum use

```text
x_(h,r) = h*(10^r-1),
a_(h,r) = H_t-r,
y_k = pi*10^k,
b_k = 1.
```

The positive integers `x_(h,r)` are distinct. The source parameter must obey

```text
X >= max x_(h,r) = 10*(10^(H_t-1)-1),
```

so `1+X` is of order `10^H_t`. The integer-coordinate local energy is exactly

```text
B(a;1) = 10*sum_{r=1}^{H_t-1}(H_t-r)^2,
```

because spacing at most `1/2` forces equal integer coordinates. Even under the
best possible assumption that the `y_k` local energy contains only its `N_t`
diagonal terms, Lemma 2.4's right side has square-root size at least comparable
to

```text
10^(H_t/2) * sqrt(N_t*H_t^3),
```

far above `H_t*N_t`. This does not prove the sum is large; it proves the cited
inequality, with its literal range factor, cannot certify the T69 threshold.
No averaging or exceptional set is responsible for this mismatch.

The NUMDAM scan loses displayed formulas under `pdftotext`. The transcription
above was checked visually against physical PDF page 5, journal page 452, and
the integer-coordinate modification against physical PDF page 7, journal page
454. The PDF is authoritative; no OCR text is claimed.

### 6.4 B2-B3: finite-field geometric sums

Garaev's Theorem 1 takes consecutive intervals of lengths `N <= p` and
`M <= ord_p(g)`, with `M < p^(2/3)`, and writes its double sum as `N*M*Delta`,
where

```text
Delta <= p^(o(1)) * [
  M^(-3/8)
  + (p/(N*M^(5/2)))^(1/4)
  + (p/(N^(4/3)*M^(7/3)))^(3/16)
  + (p/(N^2*M^(3/2)))^(1/4)].
```

Kerr's Theorem 2 treats one incomplete geometric sum
`sum_{n=1}^L e_p(lambda*g^n)`, uniformly in nonzero `lambda`, and gives the
three displayed cases involving `p^(1/8)` or `p^(1/4)`, the order of `g`, and
the powers `71/96`, `73/96`, and `49/96`.

For fixed `(h,r)`, Kerr's shape matches the T69 powers after replacing the
real phase by a rational phase and taking `g=10`. That replacement is not in
the theorem. The largest T69 integer frequency is below `10^(N_t+1)`, while
the total absolute coefficient mass is polynomial in `N_t`. To transfer the
whole sum with error `O(H_t*N_t)` requires at least

```text
|pi-a/p| <= 10^(-N_t) * N_t^(-O(1)).
```

At ordinary `p^(-2)` rational-approximation scale this forces `p` to be at
least of order `10^(N_t/2)` up to polynomial factors. Then `N_t` and `H_t`
are only logarithmic in `p`; Garaev's interval savings are trivial and Kerr's
positive power of `p` is exponentially larger than the trivial length.
Neither source supplies primes simultaneously satisfying this approximation
and a suitable multiplicative order of 10.

### 6.5 L1: sparse-modulus averaging is the wrong average

Baker--Munsch--Shparlinski Theorem 1.1 assumes integer moduli
`m_j=j^(alpha+o(1))`, the range `Q^alpha <= N <= Q^(2*alpha)`, and averages
the squared coefficient sum over `j <= Q` and all reduced residues modulo
`m_j`. Its bound is expressed using the ordinary and asymmetric additive
energies of `{m_1,...,m_Q}` and a `Q^(o(1))` factor.

The candidate moduli `10^r-1` have exponential, not polynomial, growth. The
source phase is rational and averaged over all reduced residues; it has no
evaluation at the irrational `pi`. Its inner coefficients occupy a
consecutive interval, whereas representing `10^k` by sparse coefficients
requires an ambient interval reaching `10^N_t`. These are independent literal
mismatches.

## 7. Terminal mismatch

No retained theorem reaches `(AGG)` or `(DISC)`. The exact narrowest unmet
input is the one-sided pooled fixed-point estimate

```text
there exists a real C >= 0, chosen before all scales, such that
for every natural t,

  Re(sum_{h=1}^{10} sum_{r=1}^{H_t-1} (H_t-r)
       sum_{k=0}^{N_t-r-1}
         e(h*(10^r-1)*10^k*pi))
    <= C*H_t*N_t,                                      (FP)

where N_t=4*2^t+1 and H_t=ceil(sqrt(N_t)).
```

`(FP)` would imply T69's literal aggregate condition with the fully tracked
constant `K=10+2*C`. It is weaker than an absolute-value bound and weaker than
uniform pooled half-arc discrepancy. Aistleitner--Fukuyama supplies the right
finite scale only after averaging both the phase and arc origin.
Bombieri--Iwaniec can retain the fixed phase, but its literal range factor is
exponential in `H_t`. The irreducible missing input is therefore fixed-point
pooled cancellation for the structured multipliers, with a constant uniform
in `t`; it is not maximality, endpoint convention, or an untracked factor of
ten.

This is an exact terminal mismatch, not an assertion of `(FP)`, T69's premise,
T29, C2, C3, or C1.

## 8. Replay

From a directory containing only the delivered artifacts, run

```sh
sh verify_sources.sh
```

The script checks every retained hash and text-extractable theorem marker. For
Bombieri--Iwaniec, manually inspect physical PDF pages 5-7 (journal pages
452-454), because the scan's displayed formulas are not preserved by
`pdftotext`.
