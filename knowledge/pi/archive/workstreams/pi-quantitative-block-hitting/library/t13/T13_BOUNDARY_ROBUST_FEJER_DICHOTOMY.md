# T13: Boundary-robust Fejer obstruction at exact decimal deadlines

Status: `proof sketch` (a self-contained paper proof, not a Lean
formalization).

## 1. Provenance and scope

- Agenda item: T13, serving G9.
- Canonical source: `knowledge/pi/statements/pi-quantitative-block-hitting.txt`.
- Canonical source SHA-256:
  `ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`.
- Original source URL: none. The problem is a local formulation, and the
  canonical source file records its provenance.
- Reused accepted formal result T8:
  `knowledge_library/t8/PiNoV1NaturalScaleResonance.lean`, SHA-256
  `19fc75163f95684a69b6bf5bb26534610a81b6d492e4400840f6c745a1b262ad`.
- Reused accepted proof note T11:
  `knowledge_library/t11/T11_COUNT_SENSITIVE_FOURIER_TRANSFER.md`, SHA-256
  `81a0212fbc52311b254a28cffc83bfc2c1cb11514758475aa9636a9ff1751673`.
- The decimal-cylinder bridge used in the T8 specialization was
  machine-checked in
  `knowledge_library/t6/PiNaturalScaleResonanceObstruction.lean`, SHA-256
  `491b7db1073e28b75d911a39e8718aa79eaca84689e1fd053d37426d0684f8ff`.

The result below is a necessary condition for an empty cylinder. It adds
boundary accounting to T11 and applies the result to the exact bad lengths
and deadlines supplied by T8. It does not estimate either resulting branch
for the fixed orbit of pi.

## 2. Normalized statement and quantifiers

Fix the following data:

- an integer `k >= 1` and `q=10^k`;
- an integer `N >= 1` and circle points `x_0,...,x_(N-1)`;
- a label `a in {0,...,q-1}` and its half-open cylinder `I_a`;
- a real circular boundary width `delta` and an integer cutoff `M` satisfying

```text
0 < delta <= 1/(2q),                 (2.1)
(M+1) delta >= 2q.                   (2.2)
```

If `I_a` contains none of the `N` points, then either

```text
at least N/(4q) point-indices are within circular distance delta
of one of the two endpoints of I_a,                            (2.3)
```

or

```text
sum_(0<|h|<=M)
  (1-|h|/(M+1)) |sin(pi h/q)|/(pi |h|)
  * |sum_(n=0)^(N-1) exp(2 pi i h x_n)|
    >= N/(2q).                                             (2.4)
```

The cardinality in (2.3) counts indices, hence repeated points count with
multiplicity. The absolute values of the inner sums in (2.4) are complex
moduli. There is one coefficient for each aggregated signed frequency `h`,
not one term for each ordered pair producing `h`.

### Quantifier and convention audit

- `N>=1`; the empty list is excluded because proportions would be vacuous.
- The circle is used intrinsically, including for the cylinder crossing zero.
- The cylinder is half-open, but both of its topological boundary points enter
  the boundary neighborhood.
- The boundary neighborhood uses strict distance `<delta`; its complement has
  distance `>=delta`, exactly as required by the pointwise estimate.
- `M` is a nonnegative integer. Conditions (2.1)-(2.2) in fact force a
  positive cutoff here.
- Empty means no occurrence among these `N` indexed starts, not global
  absence from an infinite sequence.
- The theorem is for the canonical decimal choice `q=10^k`. The finite
  Fourier proof works for every integer `q>=2`, but that sibling generality is
  not used to alter the agenda item's quantifiers.

## 3. Circle, cylinders, and both boundary points

Let

```text
T = R/Z,                    e(t)=exp(2 pi i t),
d_T(x,y)=inf_(m in Z) |x-y-m|,
||t||_T=d_T(t,0).
```

Haar probability measure on `T` is denoted by `dt`. For
`a in {0,...,q-1}`, define

```text
b_a     = a/q mod 1,
b_(a+1) = (a+1)/q mod 1,
I_a     = [a/q,(a+1)/q) mod 1,
partial I_a = {b_a,b_(a+1)}.
```

For `a=q-1`, the second endpoint is `0 mod 1`; it is not replaced by the real
number `1` in distance calculations. Define the circular neighborhood and its
empirical count by

```text
U_(a,delta)
  = {x in T : min(d_T(x,b_a),d_T(x,b_(a+1))) < delta},

B_(a,delta)
  = #{0 <= n < N : x_n in U_(a,delta)}.                       (3.1)
```

Thus being outside `U_(a,delta)` means being at circular distance at least
`delta` from both boundary points. No representative-dependent interval
condition is used.

## 4. Fejer kernel and aggregated triangular coefficients

For an integer `M>=0`, use the normalized Fejer kernel

```text
F_M(t) = 1/(M+1) |sum_(r=0)^M e(rt)|^2.                       (4.1)
```

Expanding the square first gives ordered pairs only as an intermediate
calculation:

```text
F_M(t)
 = 1/(M+1) sum_(r=0)^M sum_(s=0)^M e((r-s)t).
```

For a fixed signed integer `h` with `|h|<=M`, exactly `M+1-|h|` pairs satisfy
`r-s=h`. Aggregating all equal frequencies therefore gives the triangular
Fourier expansion

```text
F_M(t)
 = sum_(|h|<=M) phi_M(h)e(ht),
phi_M(h)=1-|h|/(M+1).                                        (4.2)
```

In particular `F_M>=0` and `integral_T F_M=1`. Define the convolution

```text
P_(a,M)(x) = integral_T 1_(I_a)(x-t) F_M(t) dt.               (4.3)
```

Since (4.2) is a finite sum, direct integration gives the single-frequency
expansion

```text
P_(a,M)(x)=sum_(|h|<=M) c_(a,h)e(hx),
c_(a,h)=phi_M(h) hat(1_(I_a))(h),                             (4.4)
```

where `hat(f)(h)=integral_T f(y)e(-hy)dy`. The interval coefficients are

```text
hat(1_(I_a))(0)=1/q,

hat(1_(I_a))(h)
 = [e(-ha/q)-e(-h(a+1)/q)]/(2 pi i h)
 = e(-h(a+1/2)/q) sin(pi h/q)/(pi h)       (h != 0).          (4.5)
```

Consequently

```text
c_(a,0)=1/q,
|c_(a,h)|
 = (1-|h|/(M+1)) |sin(pi h/q)|/(pi |h|)    (0<|h|<=M).       (4.6)
```

The modulus in (4.6) is independent of the cylinder label `a`. Also
`c_(a,-h)=conjugate(c_(a,h))`, so `P_(a,M)` is real-valued. Equations
(4.2), (4.4), and (4.6) are the required aggregated triangular coefficients;
the ordered-pair indexing has disappeared.

## 5. Pointwise tail estimate away from both boundaries

Represent `t in T` by `u in [-1/2,1/2]`. Away from `u=0`, the geometric-sum
formula in (4.1) gives

```text
F_M(u)
 = 1/(M+1) [sin(pi(M+1)u)/sin(pi u)]^2.
```

On this interval, `|sin(pi u)|>=2|u|`, while the numerator has modulus at
most one. Hence

```text
F_M(u) <= 1/[4(M+1)u^2]             (0<|u|<=1/2).             (5.1)
```

For `0<delta<=1/2`, integration of (5.1) on both sides of zero yields

```text
integral_(||t||_T>=delta) F_M(t)dt
 <= 2 integral_delta^(1/2) du/[4(M+1)u^2]
 = [1/delta-2]/[2(M+1)]
 <= 1/[2(M+1)delta].                                        (5.2)
```

Suppose `x` has circular distance at least `delta` from both points of
`partial I_a`. If `||t||_T<delta`, the short circular arc from `x` to `x-t`
crosses neither boundary point. Thus the two points lie in the same component
of `T \ partial I_a`, and

```text
1_(I_a)(x-t)=1_(I_a)(x).
```

Because `F_M` is nonnegative with mass one, the discrepancy can only come
from the tail in (5.2):

```text
|P_(a,M)(x)-1_(I_a)(x)|
 <= 1/[2(M+1)delta].                                        (5.3)
```

This is a circular statement away from both endpoints. Equality sets in the
integration variable have Haar measure zero, so the half-open convention
does not change the estimate.

## 6. Summed error with boundary accounting

Put

```text
A_a = #{0 <= n < N : x_n in I_a},
B_a = B_(a,delta),
epsilon = 1/[2(M+1)delta],
E_a = sum_(n=0)^(N-1) P_(a,M)(x_n).                           (6.1)
```

For the `N-B_a` indices outside the boundary neighborhood, (5.3) bounds the
error by `epsilon`. For each of the remaining `B_a` indices, the elementary
bounds `0<=P_(a,M)<=1` and `0<=1_(I_a)<=1` bound the error by one. Therefore

```text
|E_a-A_a| <= B_a+(N-B_a)epsilon <= B_a+N epsilon.             (6.2)
```

This is the promised summed error bound. When `B_a=0`, it specializes to the
all-points-separated estimate in T11.

Define the ordinary complex exponential sums

```text
S_h = sum_(n=0)^(N-1) e(h x_n),                 h in Z.       (6.3)
```

Summing (4.4) over the points gives the exact estimator identity

```text
E_a = N/q + sum_(0<|h|<=M) c_(a,h) S_h.                       (6.4)
```

No real part has been substituted for a complex norm. By the complex triangle
inequality and (4.6),

```text
W_M
 := sum_(0<|h|<=M)
      (1-|h|/(M+1)) |sin(pi h/q)|/(pi |h|) |S_h|
  = sum_(0<|h|<=M) |c_(a,h)| |S_h|
 >= |sum_(0<|h|<=M) c_(a,h)S_h|
  = |E_a-N/q|.                                                (6.5)
```

The last absolute value may be viewed as either a real absolute value or the
complex modulus of the same real number, but every individual `S_h` in the
exposed weighted sum is controlled by its complex modulus.

## 7. Explicit finite dichotomy

**Theorem 7.1 (empty-cylinder dichotomy).** Under (2.1)-(2.2), if `A_a=0`,
then

```text
B_(a,delta) >= N/(4q)                  (boundary branch)      (7.1)
```

or

```text
W_M >= N/(2q).                         (Fourier branch)       (7.2)
```

**Proof.** Condition (2.2) gives

```text
epsilon=1/[2(M+1)delta] <= 1/(4q).                           (7.3)
```

Suppose the boundary branch fails, so `B_a<N/(4q)`. Since `A_a=0`, (6.2) and
(7.3) imply

```text
0 <= E_a <= B_a+N epsilon < N/(4q)+N/(4q)=N/(2q).            (7.4)
```

It follows that

```text
|E_a-N/q|=N/q-E_a>N/(2q).
```

Now (6.5) gives `W_M>N/(2q)`, which implies the displayed weak inequality
(7.2). This proves the dichotomy. QED

All constants are literal numerals. No asymptotic notation or hidden constant
occurs in the theorem.

## 8. Fully numerical cutoff and width

For every `q=10^k`, one allowed choice is

```text
delta_q = 1/(4q),
M_q = 8q^2.                                                   (8.1)
```

Indeed `delta_q<=1/(2q)` and

```text
(M_q+1)delta_q=(8q^2+1)/(4q)>=2q.                            (8.2)
```

Thus an empty cylinder forces either

```text
#{n<N : d_T(x_n,partial I_a)<1/(4q)} >= N/(4q),              (8.3)
```

where distance to a two-point set means the minimum of the two circular
distances, or

```text
sum_(0<|h|<=8q^2)
  (1-|h|/(8q^2+1)) |sin(pi h/q)|/(pi |h|)
  * |sum_(n=0)^(N-1) exp(2 pi i h x_n)|
    >= N/(2q).                                               (8.4)
```

## 9. Contrapositive cover criterion

The exact contrapositive of Theorem 7.1 is useful and does not assert a
converse. If, for one label `a`,

```text
B_(a,delta)<N/(4q) and W_M<N/(2q),                            (9.1)
```

then `A_a>0`. Since `W_M` is independent of `a`, if

```text
W_M<N/(2q)
```

and `B_(a,delta)<N/(4q)` holds for every `a in {0,...,q-1}`, then every one of
the `q` cylinders contains at least one of the `N` points.

For a base-ten orbit, hitting every `q=10^k` cylinder among starts
`0<=n<N` means that every length-`k` word is fully contained in the prefix of
length `N+k-1`. In particular, at the canonical deadline

```text
D=C k 10^k,                    N=D-k+1,                       (9.2)
```

the criterion gives full containment by exactly `D`, not merely a bound on
the starting index.

## 10. T8 specialization at unbounded bad lengths

Let

```text
x_n={10^n pi} in T.
```

T8's machine-checked theorem
`Theory.PiDigits.PiNoV1NaturalScaleResonance.not_C1_implies_unbounded_naturalScale_resonance`
states, in particular, that literal `not C1` implies the following. For every
natural numbers `C,K` with `C>=1` and `K>=1`, there are `k>=K` and a length-`k`
decimal word `w` such that

```text
there is no n with n+k<=C k 10^k at which w occurs.           (10.1)
```

T8 also supplies its earlier single-frequency resonance, but that additional
conclusion is not used to derive the present dichotomy.

For the `k,w` supplied by T8, set

```text
q=10^k,
D=C k q,
N=D-k+1,
a=sum_(j=0)^(k-1) w_j 10^(k-1-j).                            (10.2)
```

Because `C>=1` and `k>=1`, one has `k<=D` and `N>=1`. Elementary natural-number
arithmetic gives the exact equivalence

```text
n<N  iff  n+k<=D.                                            (10.3)
```

The machine-checked decimal-cylinder bridge used in T6 says that
`x_n in I_a` implies that the next `k` fractional decimal digits of pi form
`w`. This one direction is all that is needed: any point in `I_a` would give
the occurrence forbidden by (10.1). Consequently (10.1)-(10.3) imply

```text
#{0<=n<N : x_n in I_a}=0.                                   (10.4)
```

Applying Theorem 7.1 proves the following extension of T8.

**Corollary 10.1 (T8 boundary-robust obstruction).** If `not C1`, then for
every `C,K>=1` there are `k>=K`, a length-`k` word `w`, and its cylinder label
`a`, with the exact deadline parameters in (10.2), such that for every
`delta,M` satisfying

```text
0<delta<=1/(2*10^k),
(M+1)delta>=2*10^k,                                          (10.5)
```

one has

```text
#{0<=n<N : d_T({10^n pi},partial I_a)<delta}
  >= N/(4*10^k),                                             (10.6)
```

or

```text
sum_(0<|h|<=M)
  (1-|h|/(M+1)) |sin(pi h/10^k)|/(pi |h|)
  * |sum_(n=0)^(N-1) exp(2 pi i h 10^n pi)|
    >= N/(2*10^k).                                           (10.7)
```

Replacing `{10^n pi}` by `10^n pi` in (10.7) is valid because `h` is an
integer. The frequencies are ordinary signed integer frequencies, aggregated
before the exponential sums are formed.

With the fully numerical choice (8.1), Corollary 10.1 becomes

```text
delta=1/(4*10^k),
M=8*10^(2k),                                                  (10.8)
```

and forces either the proportion `1/(4*10^k)` in (10.6) or the lower bound
`N/(2*10^k)` in (10.7), at the exact number
`N=C*k*10^k-k+1` of admissible starts. Since `K` is arbitrary, these bad
lengths are unbounded.

## 11. Audit against the three rejected T12 substitutes

1. **Complex absolute values.** Equations (6.5), (7.2), (8.4), and (10.7)
   contain `|S_h|`, the complex modulus of each ordinary exponential sum.
   They do not control only `Re(S_h)` or only the real part of an estimator.
2. **Aggregated frequencies.** Equation (4.2) counts the ordered pairs with
   difference `h` and replaces them by the one triangular coefficient
   `1-|h|/(M+1)`. All final sums are indexed by signed frequencies `h` alone.
3. **Circular boundary accounting.** Equations (3.1), (5.3), (10.6) use
   circular distance to both topological boundary points. The wraparound
   endpoint of `I_(q-1)` is `0 mod 1`; no chosen real representative can hide
   it.

These are substantive parts of the proof, not alternative formulations.

## 12. Exact limitations

- This is a necessary-only obstruction forced by an empty cylinder and, via
  T8, by `not C1` at unbounded bad lengths.
- The local contrapositive in Section 9 is proved. No converse is proved that
  turns either obstruction branch into cylinder emptiness or turns such a
  branch for pi into `not C1`.
- No upper bound is supplied for the number of pi-orbit points near the two
  boundaries in (10.6).
- No upper or lower estimate independent of the dichotomy is supplied for
  pi's weighted ordinary exponential sums in (10.7).
- In particular, the note supplies neither branch estimate needed to eliminate
  the obstruction for pi.
- The result neither proves nor refutes C1 and does not change its `open`
  status.

## References

- [T8] `knowledge_library/t8/PiNoV1NaturalScaleResonance.lean`, especially
  theorem
  `Theory.PiDigits.PiNoV1NaturalScaleResonance.not_C1_implies_unbounded_naturalScale_resonance`.
- [T11] `knowledge_library/t11/T11_COUNT_SENSITIVE_FOURIER_TRANSFER.md`,
  especially Sections 3-5.
- [T6] `knowledge_library/t6/PiNaturalScaleResonanceObstruction.lean`,
  especially
  `piOrbit_naturalScale_resonance_of_missingBefore` and
  `normalized_piOrbit_naturalScale_resonance_of_missing_fullContainment`.
