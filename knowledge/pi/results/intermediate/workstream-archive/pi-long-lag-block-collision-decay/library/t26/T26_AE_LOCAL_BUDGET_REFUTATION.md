# T26: almost-everywhere refutation of the exact T24 local budget

Status: `proof sketch`. This is a rigorous prose proof using the
machine-checked T22, T24, T16, and T18 inputs listed below. The prose argument
itself is not kernel-checked. Every verdict in this note concerns only the
Lebesgue-almost-everywhere phase sibling. It gives no estimate at `alpha=pi`
and no conclusion about C1.

## 1. Provenance and claim boundary

The canonical question is the locally formulated statement vendored as
`CANONICAL_STATEMENT.txt`. It has no external source URL. Its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

The canonical question concerns ordered collisions in the decimal digits of
the fixed number pi. This note studies a sibling only: in T22 and T24, replace
the orbit value `Real.pi` in the Fourier argument `(k:Real)*Real.pi` by a
Lebesgue-random `alpha` in `[0,1)`. The universal circle constant in

```text
e(x) := exp(2*pi*i*x)
```

is not replaced. The T22 arithmetic exclusion, coefficients, endpoint
cutoffs, and ordered orientations are unchanged.

The exact machine-checked inputs are:

1. T22,
   `TheoryLib.PiLongLagBlockCollisionDecay.T22T22SparseFrequencyCutoff`,
   source SHA-256
   `73b49990d59e2c446b121eee977a04b9bbb4806f7c47be01c384acb8bf7d1713`.
   This supplies the admissible domain, signed-frequency injectivity, both
   orientations, coefficient one, strict endpoint cutoff, and variable-phase
   `cutoffFourierSum`.
2. T24,
   `TheoryLib.PiLongLagBlockCollisionDecay.T24T24MaximalToLocalReduction`,
   source SHA-256
   `2795d228eab081360e236be14ae99c0dd8267153d39e680710732330ea586924`.
   This supplies the half-open aligned dyadic blocks, exact endpoint and block
   increments, inclusive vector L1 norm, and the local budget predicate.
3. T16,
   `TheoryLib.PiLongLagBlockCollisionDecay.T16T16FiniteWeightedGCD`, source
   SHA-256
   `4c73188eae8b457403b25ef0577d22a7c4446c539bcf72df60905bf084204aec`.
   Its theorem `longDifferenceMultiplicityWeightedGCD_le` has exact constant
   `574913232` and covers positive four-token differences in the half-open
   exponent box `0,...,N-1`, with both weak long-lag constraints.
4. T18,
   `TheoryLib.PiLongLagBlockCollisionDecay.T18T18AlmostEverywhereScaleMatchedL1`,
   source SHA-256
   `3f171dc88208dec60f8ea33957223829585b220e5623138997e8d8b571244439`.
   Its kernel-checked finite Parseval and resonance lemmas justify the same
   weighted-GCD variance calculation for any restricted subset used below.

The T25 note is an unverified `proof sketch`. It motivates testing the latest
endpoint layer, but no T25 claim is used as a premise. All layer identities
needed here are proved again.

## 2. Exact sibling statement and quantifiers

Let `lambda` be Lebesgue measure restricted to `[0,1)`, normalized so that
`lambda([0,1))=1`. Fix

```text
mu=8, c=1, Q0 in Nat, m>=1, E>=m, H=10^m.
```

For an orientation bit and core `(r,n) in Nat x Nat`, T22's exact
`N`-cutoff domain is

```text
0<r, m<=r,
not ArithmeticExcluded 8 1 Q0 m n r,
n+r<N.                                                   (2.1)
```

Both orientation bits obey the same conditions. They carry respectively the
opposite signed frequencies: `false` carries
`-(10^(n+r)-10^n)` and `true` carries `+(10^(n+r)-10^n)`. Every surviving
signed frequency has coefficient exactly one. The endpoint inequality in
(2.1) is strict.

T24 defines a block `B=(start,level)` by

```text
length(B)=2^level,
finish(B)=start+2^level,
Aligned(B) iff 2^level divides start-1.
```

Its exact variable-phase block L1 quantity is

```text
dyadicBlockL1 8 1 Q0 m B alpha
 = sum_(h=1)^H
     |cutoffFourierSum 8 1 Q0 m finish(B) h alpha
       - cutoffFourierSum 8 1 Q0 m start(B) h alpha|.     (2.2)
```

The frequency range in (2.2) is inclusive: frequency zero is absent and
`h=H=10^m` is present. The T24 local predicate at exponent `s` and constant
`B0` is

```text
B0>=0 and, for every m>=1, start>=1, level>=0 with
2^level | start-1,

dyadicBlockL1 8 1 Q0 m (start,level) alpha
 <= B0 H [2^level
      + ((start+2^level)^2-start^2) 10^(-s m)].          (2.3)
```

The predicate `LocalizedDyadicBlockBudget 8 1 Q0 alpha` requires, for every
real `0<s<1`, one `B0` independent of `m,start,level` satisfying (2.3).

The exact verdict proved below is the following.

**Almost-everywhere sibling theorem.** There is a measurable set
`Omega subset [0,1)` of Lebesgue measure one such that, simultaneously for
every `alpha in Omega` and every natural `Q0`,

```text
not LocalizedDyadicBlockBudget 8 1 Q0 alpha.             (2.4)
```

More precisely, (2.3) already fails at `s=1/2` on infinitely many aligned
level-zero blocks

```text
m=2^n,  start=E=2m,  level=0,  finish=E+1.              (2.5)
```

This is an almost-everywhere sibling refutation of T24's sufficient local
premise, not a refutation of T24's deterministic implication.

## 3. Exact latest-endpoint layer

T22's cutoff at `N` contains exactly the admissible signed frequencies whose
endpoint is strictly less than `N`. Therefore the difference between cutoffs
`E+1` and `E` contains endpoint `E`, not endpoint `E+1`.

For an endpoint-`E` core, the lag and start satisfy

```text
m<=r<=E,  n=E-r,  n+r=E.                                (3.1)
```

The positive frequency is

```text
k_r=10^E-10^(E-r)=10^(E-r)(10^r-1)>0.                  (3.2)
```

At `(mu,c)=(8,1)` every lag in (3.1) survives the arithmetic exclusion,
independently of `Q0`. Indeed, with `x=10^m-1` and
`d=10^(E-r)(10^r-1)`, one has

```text
d>=x>=9,
x^2>x+1=10^m,
d^7>=x^7>x^2>10^m.                                     (3.3)
```

The exclusion would require both `Q0<=d` and
`10^(-m)<=d^(-7)`. The last inequality in (3.3) gives the strict opposite
inequality `d^(-7)<10^(-m)`. Thus the exclusion is false for every `Q0`.

T22's `both_orientations_exact`, coefficient-one theorem, and signed
injectivity now give the disjoint signed layer

```text
Gamma_(m,E)={+k_r,-k_r : m<=r<=E},
|Gamma_(m,E)|=2a,  a=E-m+1.                             (3.4)
```

The negative sign is the ordered orientation `(E-r,E)` and the positive sign
is `(E,E-r)`. No factor of two is suppressed.

Define the exact endpoint increment

```text
D_(m,E)(h,alpha)
 := cutoffFourierSum 8 1 Q0 m (E+1) h alpha
      - cutoffFourierSum 8 1 Q0 m E h alpha.            (3.5)
```

Equations (3.2)-(3.4) prove, for every integer `h`,

```text
D_(m,E)(h,alpha)
 = sum_(r=m)^E [e(h k_r alpha)+e(-h k_r alpha)]
 = 2 sum_(r=m)^E cos(2*pi*h*k_r*alpha).                 (3.6)
```

In particular, the increment is real. Put

```text
L_(m,E)(alpha)=sum_(h=1)^H |D_(m,E)(h,alpha)|,
M_(m,E)(alpha)=sum_(h=1)^H |D_(m,E)(h,alpha)|^2,
W_(m,E)(alpha)=sum_(h=1)^H |D_(m,E)(h,alpha)|^4.        (3.7)
```

For the block `(start,level)=(E,0)`, T24 gives length `1`, finish `E+1`, and
alignment `1 | E-1`. Hence (3.5) is exactly its block increment and

```text
dyadicBlockL1 8 1 Q0 m (E,0) alpha=L_(m,E)(alpha).       (3.8)
```

The exact level-zero instance of (2.3) is therefore

```text
L_(m,E)(alpha)
 <= B0 H [1+(2E+1)10^(-s m)].                           (3.9)
```

## 4. Exact finite moments

For every integer `z`, character orthogonality on the specified half-open
probability interval is

```text
integral_[0,1) e(z alpha) d alpha = 1 if z=0, else 0.   (4.1)
```

All following sums are finite, so termwise expansion and integration are
valid.

### 4.1 Exact second moment

For each `1<=h<=H`, expanding (3.6) and using (4.1) gives

```text
integral |D_(m,E)(h,alpha)|^2 d alpha
 = #{(omega,omega') in Gamma_(m,E)^2 : h omega=h omega'}
 = |Gamma_(m,E)|=2a.                                   (4.2)
```

The last equality uses `h>=1` and T22's signed-frequency injectivity. Summing
over all `H` inclusive frequencies proves

```text
integral M_(m,E) d alpha=2Ha.                           (4.3)
```

### 4.2 Exact fourth moment

For fixed positive `h`, multiplication by `h` does not change an integer
additive relation. Thus

```text
integral |D_(m,E)(h,alpha)|^4 d alpha
 = #{(w1,w2,w3,w4) in Gamma_(m,E)^4 : w1+w2=w3+w4}.     (4.4)
```

We now count (4.4) exactly. Write `A=10^E`, `j=E-r`, so

```text
Gamma_(m,E)={+/- (A-10^j) : 0<=j<=a-1}.                (4.5)
```

In an equality of two sums from (4.5), move the four `A` terms to one side.
If their signed coefficient were nonzero, its absolute value would be at
least `2A`. The four remaining powers have exponents at most `E-1`, so their
total absolute value is at most `4*10^(E-1)<2A`. Therefore the coefficient of
`A` is zero. The two sides have the same sign count, which is `2`, `0`, or
`-2`.

For sign count `2`, both summands on each side are positive. Equality reduces
to

```text
10^i+10^j=10^k+10^l.                                   (4.6)
```

Decimal coefficients are at most two, so no carrying occurs and the two
unordered multisets of exponents agree. The `a` diagonal ordered pairs have
one representation each; the `a(a-1)` off-diagonal ordered pairs occur in
pairs. Their additive energy is

```text
a+4*binom(a,2)=2a^2-a.                                  (4.7)
```

The sign count `-2` contributes the same quantity.

For sign count zero, each side contains one positive and one negative layer
frequency. There are two orders on each side, for an overall factor four.
After fixing those orders, equality reduces to equality of differences of
powers. The zero difference has `a` representations and contributes `a^2`.
Every nonzero ordered difference `10^i-10^j` is unique: its sign determines
which exponent is larger, its exact decimal valuation determines the smaller
exponent, and the quotient determines their gap. The `a^2-a` nonzero ordered
pairs therefore contribute `a^2-a`. This sector contributes

```text
4[a^2+(a^2-a)]=8a^2-4a.                                (4.8)
```

Adding the three sign-count sectors gives the exact additive energy

```text
2(2a^2-a)+(8a^2-4a)=12a^2-6a.                          (4.9)
```

Equations (4.4) and (4.9), summed over exactly `H` frequencies, prove

```text
integral W_(m,E) d alpha=H(12a^2-6a).                  (4.10)
```

This calculation includes both ordered signs and the inclusive endpoint
`h=H`.

## 5. Parameter-uniform concentration of the second moment

For `d>0`, let

```text
nu(d)=#{(omega,omega') in Gamma_(m,E)^2 : omega-omega'=d}. (5.1)
```

Expanding the centered energy and using (4.1) exactly as in T18 gives

```text
Var(M_(m,E))
 = 2 sum_(d,e>0) nu(d)nu(e)
       floor(H gcd(d,e)/max(d,e)).                      (5.2)
```

For completeness, the floor in (5.2) is exact. Write
`d=g d0`, `e=g e0`, where `g=gcd(d,e)` and `gcd(d0,e0)=1`. The positive
solutions of `h d=k e` are

```text
h=e0*l, k=d0*l,
1<=l<=floor(H g/max(d,e)).                              (5.3)
```

In the centered expansion there are two surviving sign choices, `+hd-ke=0`
and `-hd+ke=0`; the same-sign choices cannot vanish because all four
integers are positive. This proves both the factor two and the exact
resonance count in (5.2).

Here is the exact domain map needed to apply T16. Every `omega` in the layer
is the frequency of one T22 ordered record whose two orbit exponents lie in
`0,...,E`, whose weak lag is at least `m`, and whose endpoint is exactly `E`.
Call that unique record `q(omega)`. An ordered positive difference
`(omega,omega')` maps to T16's four-token vector

```text
(first(q(omega)), second(q(omega')),
 second(q(omega)), first(q(omega'))).                    (5.4)
```

Its T16 signed value is `omega-omega'>0`. Both weak lag constraints are
retained, all four exponents lie in the half-open box `0,...,(E+1)-1`, and
the four coordinates recover the two ordered records, so (5.4) is injective.
Thus the weighted sum in (5.2), after removing the floor, is a sub-sum of
T16's exact `longDifferenceWitnessWeightedGCD m (E+1)`. The GCD kernel is
nonnegative. With

```text
Cstar=574913232,                                        (5.5)
```

T16 gives

```text
sum_(d,e>0) nu(d)nu(e) gcd(d,e)/max(d,e)
 <= Cstar (E+1)^4.                                     (5.6)
```

Since `floor(x)<=x`, (5.2) and (5.6) prove the uniform variance estimate

```text
Var(M_(m,E)) <= 2 Cstar H (E+1)^4.                     (5.7)
```

No phase value, Diophantine estimate, or independence assumption occurs in
(5.6)-(5.7).

By (4.3), the event `M_(m,E)<Ha` forces a deviation of more than `Ha` from
the mean `2Ha`. Chebyshev's inequality and (5.7) therefore give

```text
lambda{alpha : M_(m,E)(alpha)<Ha}
 <= 2 Cstar (E+1)^4/(H a^2).                            (5.8)
```

Markov's inequality applied to the nonnegative quantity `W` and the exact
identity (4.10) gives, for every real `T>0`,

```text
lambda{alpha : W_(m,E)(alpha)>T H(12a^2-6a)} <= 1/T.   (5.9)
```

These are parameter-uniform finite estimates for the almost-everywhere
sibling. The functions `D`, `L`, `M`, and `W` are finite sums of continuous
trigonometric functions and their absolute values, so all events in
(5.8)-(5.9) are measurable.

## 6. Borel-Cantelli on wide latest-endpoint layers

For integers `n>=1`, choose the exact sequence

```text
m_n=2^n, E_n=2m_n, a_n=m_n+1, H_n=10^m_n.              (6.1)
```

These are wide layers: the lag range is the inclusive interval
`m_n,...,2m_n`, with `m_n+1` positive frequencies and both orientations.

For the lower-second-moment failure event, (5.8) and
`2m+1<=3m`, `m+1>=m` give

```text
lambda{M_(m_n,E_n)<H_n a_n}
 <= 162 Cstar m_n^2/10^m_n.                             (6.2)
```

Since `2^n>=2n` for `n>=1`,

```text
162 Cstar m_n^2/10^m_n
 <= 162 Cstar 4^n/100^n
 = 162 Cstar 25^(-n).                                  (6.3)
```

The series in (6.3) converges.

For the upper-fourth-moment failure event, use (5.9) with `T=n^2`:

```text
lambda{W_(m_n,E_n)>n^2 H_n(12a_n^2-6a_n)} <= 1/n^2.    (6.4)
```

This series also converges. The first Borel-Cantelli lemma, which needs no
independence, proves that for almost every `alpha`, both inequalities

```text
M_(m_n,E_n)(alpha)>=H_n a_n,
W_(m_n,E_n)(alpha)<=n^2 H_n(12a_n^2-6a_n)              (6.5)
```

hold for all sufficiently large `n`.

Explicitly, let `A_n` and `B_n` be the two measurable failure events in
(6.2) and (6.4), and set

```text
Omega=[0,1) \ (limsup_n A_n union limsup_n B_n).         (6.6)
```

Both limsup sets are measurable and have measure zero by Borel-Cantelli, so
`Omega` is measurable and has measure one. Since the layer is independent of
`Q0`, this single `Omega` is common to every natural `Q0`.

For nonnegative `x_h=|D_(m,E)(h,alpha)|`, Holder's inequality gives

```text
(sum_h x_h^2)^3 <= (sum_h x_h)^2 (sum_h x_h^4).         (6.7)
```

On (6.5), `M>=Ha>0`, so at least one `x_h` is positive and hence `W>0`;
division by `W^(1/2)` is legitimate. Apply (6.7) to (6.5). Since
`12a^2-6a<=12a^2`, every `alpha in Omega` satisfies

```text
L_(m_n,E_n)(alpha)
 >= M_(m_n,E_n)(alpha)^(3/2)/W_(m_n,E_n)(alpha)^(1/2)
 >= H_n sqrt(a_n)/(sqrt(12) n)                         (6.8)
```

for all sufficiently large `n`.

## 7. Comparison with the exact T24 budget

Fix `s=1/2`. At the level-zero block in (6.1), the exact right-hand bracket
in (3.9) is

```text
1+(2E_n+1)10^(-m_n/2)
 =1+(4m_n+1)10^(-m_n/2).                               (7.1)
```

For every integer `m>=4`,

```text
(4m+1)10^(-m/2)<=1.                                    (7.2)
```

For an explicit check, the left side is `17/100<1` at `m=4`; its ratio at
successive integers is

```text
[(4m+5)/(4m+1)]/sqrt(10)<1
```

because `(4m+5)/(4m+1)<=21/17` for `m>=4` and `sqrt(10)>3`.
Thus the bracket in (7.1) is at most two.

Combining (6.8) and (7.1)-(7.2), for every `alpha in Omega`,

```text
L_(m_n,E_n)(alpha)
 / [H_n(1+(4m_n+1)10^(-m_n/2))]
 >= sqrt(2^n+1)/(2 sqrt(12) n)                         (7.3)
```

for all sufficiently large `n`. The right side tends to infinity. For
example, squaring reduces this to the elementary exponential domination
`2^n/n^2 -> infinity`.

Consequently, for almost every `alpha` and every proposed finite `B0>=0`,
some block in (2.5) violates the exact T24 inequality (3.9) at `s=1/2`.
Because Section 3 proved that every such layer is independent of `Q0`, the
same full-measure set works simultaneously for all natural `Q0`.

## 8. Terminal metric verdict

**Proved almost-everywhere sibling refutation.** There is one measurable
full-measure set `Omega subset [0,1)` such that

```text
for every alpha in Omega and every Q0 in Nat,
not LocalizedDyadicBlockBudget 8 1 Q0 alpha.             (8.1)
```

The failure occurs already for `s=1/2` and the exact aligned level-zero
blocks

```text
m=2^n, start=E=2m, level=0, finish=E+1,
lag range m<=r<=E,
frequencies 1<=h<=10^m inclusive.                       (8.2)
```

The proof retains T22's strict endpoint convention, both ordered
orientations, coefficient one, arithmetic exclusion, and T24's half-open
block and translated-grid alignment. Its finite moment constants are

```text
mean(M)=2Ha,
integral W=H(12a^2-6a),
Var(M)<=2*574913232*H*(E+1)^4.                           (8.3)
```

Thus T24's uniform local premise is too strong even in the solved
Lebesgue-random analogue, although T18's weaker global scale-matched cutoff
bound remains compatible almost everywhere. This conclusion is only about
the almost-everywhere sibling. It supplies no estimate for the fixed phase
`alpha=pi`, no estimate for decimal blocks of pi, and no conclusion about C1.
