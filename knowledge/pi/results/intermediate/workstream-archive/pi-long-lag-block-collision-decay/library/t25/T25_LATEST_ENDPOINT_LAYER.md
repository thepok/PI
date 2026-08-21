# T25: one latest-endpoint layer at the fixed phase pi

Status: `proof sketch`. The finite identities and inequalities below are
proved in rigorous prose. The cited T22, T4, and T16 declarations are
machine-checked inputs, but this note itself is not kernel-checked. The T23
note is used only as unverified motivation.

## 1. Provenance, claim boundary, and imported inputs

The canonical question is the locally formulated problem in
`knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`; there is no original
external source URL. Its verified SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

It asks whether, for every real `s` with `0<s<1`, one constant `C_s>=1`
works for all positive integers `m,N` in

```text
R_pi(m,N) <= C_s [N+N^2 10^(-s m)].
```

Here pairs are ordered, indices lie in `0,...,N-1`, and the weak long-lag
condition is `|i-j|>=m`. The additive `N` term and the quantifier order
`forall s, exists C_s, forall m,N` are part of the canonical statement.

This note does not estimate `R_pi`. It studies one successor layer of the
residual sparse Fourier cutoff, a conditional reduction target related to
the canonical statement's recorded sibling A12. It proves no instance of C1
and asserts no verdict on C1.

The machine-checked inputs and separately labeled motivation are:

1. T22, module
   `TheoryLib.PiLongLagBlockCollisionDecay.T22T22SparseFrequencyCutoff`,
   source SHA-256
   `73b49990d59e2c446b121eee977a04b9bbb4806f7c47be01c384acb8bf7d1713`.
   In particular, this note uses its exact endpoint, orientation,
   injectivity, coefficient-one, and cutoff-sum interface.
2. T4, module
   `TheoryLib.PiLongLagBlockCollisionDecay.T4T4PublishedIrrationalityOnset`,
   source SHA-256
   `73a70fc981bc5856e6c52f3c27143d1a54d84373f830c2b1d37faeb2fdbd71de`.
   Its fixed-pi conclusion is conditional on the explicit external premise
   `IrrationalityMeasureBelow Real.pi 8`. The retained publication is
   Zeilberger--Zudilin, *The Irrationality Measure of Pi is at most
   7.103205334137...*, DOI
   <https://doi.org/10.2140/moscow.2020.9.407>, retained PDF SHA-256
   `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
   The source premise is literature evidence, not a theorem proved by Lean.
3. T16, module
   `TheoryLib.PiLongLagBlockCollisionDecay.T16T16FiniteWeightedGCD`, source
   SHA-256
   `4c73188eae8b457403b25ef0577d22a7c4446c539bcf72df60905bf084204aec`.
   Its named theorem gives the kernel-checked constant `574913232` for the
   exact long-difference multiplicity-weighted GCD sum.
4. The T23 note, SHA-256
   `515e1ab4712172fcf767ce86648b0a7f979103fe1148cd50671991fab0cc3edc`,
   is an unverified `proof sketch`. No assertion unique to T23 is used as a
   premise.

## 2. Parameters and exact latest-endpoint domain

Fix

```text
m,E,Q0 in N,   m>=1,   E>=m,   H:=10^m,
mu:=8,         c:=1,   alpha:=pi.
```

The cutoff at `N` contains precisely the T22 frequencies whose endpoint is
strictly less than `N`. Therefore the latest endpoint introduced between
cutoffs `E` and `E+1` is exactly endpoint `E`, not `E+1`.

Define the surviving lag set

```text
A_(m,E,Q0)
 := {r in N : m<=r<=E and
      not ArithmeticExcluded 8 1 Q0 m (E-r) r},          (2.1)
a_(m,E,Q0) := #A_(m,E,Q0).
```

For `r` in this set, the start is

```text
n_r:=E-r,                                                 (2.2)
```

so `0<=n_r<=E-m` and `n_r+r=E`. Put

```text
k_r:=10^E-10^(E-r)=10^(E-r)(10^r-1)>0.                  (2.3)
```

T22's `mem_cutoff_succ_not_cutoff_iff_endpoint`,
`both_orientations_exact`, and signed-frequency injectivity give the disjoint
layer

```text
Lambda_(E+1) \ Lambda_E = {+k_r,-k_r : r in A_(m,E,Q0)}, (2.4)
```

with coefficient exactly one at each signed frequency. Thus the layer has
exactly `2a_(m,E,Q0)` elements. The two signs are the two ordered
orientations: `false` represents `(E-r,E)` and has frequency `-k_r`; `true`
represents `(E,E-r)` and has frequency `+k_r`. They are distinct because
`k_r>0`. Distinct lags give distinct positive frequencies by T22's
injectivity theorem.

For the parameters `(mu,c)=(8,1)`, every lag in the displayed interval
actually survives, independently of `Q0`. Here is the elementary check,
included rather than imported from an unverified note. The structured
denominator is

```text
d_r=10^(E-r)(10^r-1).
```

`ArithmeticExcluded 8 1 Q0 m (E-r) r` requires both `Q0<=d_r` and

```text
H^(-1) <= d_r * d_r^(-8)=d_r^(-7).                      (2.5)
```

Let `x=10^m-1`. Since `r>=m`, one has `d_r>=10^r-1>=x>=9`. Also

```text
x^2>x+1=10^m=H,
```

because `x^2-x-1>0` for `x>=9`. Hence `d_r^7>=x^7>x^2>H`, and therefore
`d_r^(-7)<H^(-1)`, contradicting (2.5). Consequently

```text
A_(m,E,Q0)={m,m+1,...,E},
a_(m,E,Q0)=E-m+1.                                       (2.6)
```

This calculation uses only the definition of the exclusion predicate; it
does not assert the external T4 premise.

If `E<m`, the same endpoint audit gives an empty layer. All substantive
claims below concern `E>=m`.

## 3. Pairing the two ordered orientations

Write

```text
e(x):=exp(2*pi*i*x).
```

This is exactly the normalization of `Theory.PiDigits.T27.phase`: its phase
at integer frequency `h` and real argument `x` is `e(hx)`. Define the latest
endpoint increment

```text
Delta_E(h;pi)
 := cutoffFourierSum 8 1 Q0 m (E+1) h pi
    -cutoffFourierSum 8 1 Q0 m E h pi.                  (3.1)
```

The nested finite cutoffs, (2.4), and coefficient one imply, for every
integer `h`,

```text
Delta_E(h;pi)
 = sum_(r=m)^E [e(h k_r pi)+e(-h k_r pi)].              (3.2)
```

The identity `e(x)+e(-x)=2 cos(2*pi*x)` now pairs the two literal ordered
orientations and proves

```text
Delta_E(h;pi)
 = 2 sum_(r=m)^E cos(2*pi*h*k_r*pi).                    (3.3)
```

In particular, the increment is real. There is no orientation factor left
implicit in (3.3): the coefficient `2` is exactly the contribution of the
two ordered orientations.

## 4. Inclusive-frequency second moment

The required frequency set is the inclusive interval

```text
1<=h<=H=10^m,                                           (4.1)
```

which contains exactly `H` integers. Frequency zero is absent and the
endpoint `h=H` is present. Define

```text
C_H(x):=sum_(h=1)^H cos(2*pi*h*x),
M_(m,E):=sum_(h=1)^H |Delta_E(h;pi)|^2.                 (4.2)
```

Because (3.3) is real, its complex norm squared is its ordinary square. Use

```text
cos(x)^2=(1+cos(2x))/2,
2 cos(x)cos(y)=cos(x-y)+cos(x+y).
```

Expanding (3.3), with every endpoint retained, gives the exact identity

```text
M_(m,E)
 = 2H a
   +2 sum_(r=m)^E C_H(2 k_r pi)
   +4 sum_(m<=r<u<=E)
       [C_H((k_u-k_r)pi)+C_H((k_u+k_r)pi)],             (4.3)
```

where `a=E-m+1` by (2.6).

For a sign audit, let

```text
Omega_(m,E):={+k_r,-k_r : m<=r<=E}.                     (4.4)
```

Then (3.2) also gives

```text
M_(m,E)
 = sum_(omega,omega' in Omega_(m,E))
     sum_(h=1)^H e(h(omega-omega')pi).                  (4.5)
```

There are `2a` zero differences `omega=omega'`, producing the explicit
diagonal `2Ha` in (4.3). For each `r`, the two ordered nonzero self-pairs
produce `2C_H(2k_r pi)`. For each unordered pair `r<u`, the eight ordered
cross-sign pairs produce four copies of the real kernel at `k_u-k_r` and
four at `k_u+k_r`. This accounts for every coefficient and proves that
(4.3) has neither a missing orientation nor a doubled endpoint.

## 5. The strongest termwise consequence of the T4 premise

For real `x`, write `||x||_T` for distance to the nearest integer. The finite
geometric sum always satisfies the triangle bound `H`; when `||x||_T>0`, it
also satisfies

```text
|sum_(h=1)^H e(hx)|
 <= min(H,1/(2||x||_T)).                                 (5.1)
```

Indeed, the triangle inequality gives `H`; the geometric-series formula has
denominator `|sin(pi*x)|`, and
`|sin(pi*x)|>=2||x||_T`. Taking real parts gives, under the same
nonintegrality hypothesis,

```text
|C_H(x)|<=min(H,1/(2||x||_T)).                           (5.2)
```

If `||x||_T=0`, the safe statement is `|C_H(x)|<=H` (indeed equality holds).

Now explicitly assume the external premise

```text
hSource : IrrationalityMeasureBelow pi 8.               (5.3)
```

T4's machine-checked conditional theorem supplies a natural `Q0` such that
`EffectiveIrrationality pi 8 1 Q0`. For every positive integer `d>=Q0`, take
a nearest integer `p` to `d*pi`. The effective-irrationality inequality gives

```text
1/d^8 < |pi-p/d|,
||d*pi||_T=|d*pi-p|>d^(-7).                             (5.4)
```

Thus `||d*pi||_T>0` for every `d>=Q0`, and

```text
|C_H(d*pi)|<=min(H,d^7/2).                              (5.5)
```

The effective-irrationality premise also implies that `pi` is irrational: if
`pi=P/D` were rational, a positive multiple `d` of `D` with `d>=Q0` would
make `||d*pi||_T=0`, contradicting (5.4). Hence the finitely many distances
with `1<=d<Q0` are also nonzero. The strongest direct cap obtained from the
exact geometric bound and T4 is

```text
B_(H,Q0)(d)
 := min(H,1/[2||d*pi||_T])    if 1<=d<Q0,
    min(H,d^7/2)              if d>=Q0.                 (5.6)
```

Since `k_u>k_r` for `r<u`, applying (5.5)-(5.6) term by term to (4.3) yields

```text
M_(m,E)
 <= 2Ha
    +2 sum_(r=m)^E B_(H,Q0)(2k_r)
    +4 sum_(m<=r<u<=E)
       [B_(H,Q0)(k_u-k_r)+B_(H,Q0)(k_u+k_r)].           (5.7)
```

This is the strongest upper bound obtained by inserting only the individual
T4 denominator estimate into the exact second-moment expansion.

For all sufficiently large `m` (depending only on `Q0`), the estimate is
ineffective on every self-sum and every cross-sum. From
`k_r>=10^m-1=x>=9` and `x^2>H`,

```text
(2k_r)^7/2>H,
(k_r+k_u)^7/2>H.                                        (5.8)
```

Once `2(10^m-1)>=Q0`, every `2k_r` and `k_r+k_u` is at least `Q0`, and (5.8)
makes its cap in (5.6) exactly `H`. T4 can then improve only some difference
terms `k_u-k_r`, never the self-sums or cross-sums. At every scale, setting
all caps to the universally valid value `H` gives the convenient coarser
bound

```text
M_(m,E)<=4H a^2.                                        (5.9)
```

The count is exact: `2Ha` from the diagonal, `2Ha` from self-sums, and
`8H*binom(a,2)` from the two kernels for every `r<u` total `4Ha^2`.

Equations (5.7)-(5.9) are upper bounds only. In particular, the large
termwise majorant is not a lower bound for the actual second moment; the real
kernels in (4.3) may cancel.

## 6. What the kernel-checked T16 theorem does and does not add

T16 defines exact positive four-token differences of two ordered long-pair
frequencies, with all four exponents in the half-open box `0,...,N-1`, both
weak lag constraints, and multiplicities given by exact witness fibers. Its
kernel-checked theorem is

```text
longDifferenceMultiplicityWeightedGCD(m,N)
 <= 574913232 N^4.                                      (6.1)
```

The kernel in (6.1) is

```text
gcd(d,e)/max(d,e).                                      (6.2)
```

It retains ordinary 2-adic, 5-adic, odd, and cyclotomic common factors. The
layer quantities `2k_r`, `k_u-k_r`, and `k_u+k_r` are among the same
sparse-decimal
two- or four-token forms, so T16 genuinely controls arithmetic
multiplicities and GCD relationships in a containing exponent box (take
`N=E+1`).

However, neither (6.1) nor any claimed T16 theorem contains the fixed phase
`pi`, the circle distance `||d*pi||_T`, or the kernel `C_H(d*pi)`. The GCD
kernel arises when equal products such as `hd=ke` are counted after averaging
a phase and applying Parseval. At one fixed phase there is no valid
implication

```text
gcd(d,e)/max(d,e) small  ==>  ||d*pi||_T large.          (6.3)
```

Combining T16 with T4 therefore gives no improvement to (5.7): T16 controls
how sparse differences relate to each other, while T4's explicit premise
controls each `||d*pi||_T` only by the size bound `d^(-7)`. A metric or
phase-averaged T16 consequence cannot be evaluated at `alpha=pi` without an
additional fixed-orbit input. Thus (5.7) is the strongest checkable termwise
fixed-pi majorant from these inputs; (5.9) is its convenient all-parameter
simplification.

This identifies a library gap, not a negative theorem about pi.

## 7. A proved nontrivial uniform range

Define the exact one-layer L1 quantity

```text
L1_(m,E):=sum_(h=1)^H |Delta_E(h;pi)|.                  (7.1)
```

Cauchy--Schwarz and (5.9) give

```text
L1_(m,E)<=sqrt(H M_(m,E))<=2Ha.                         (7.2)
```

The direct triangle inequality in (3.2) gives the same bound, since there are
`2a` unit-modulus terms at each of the `H` frequencies.

The exact level-zero local budget requested in this agenda item has start
`E`, length `1`, increment (3.1), and right-hand side

```text
L1_(m,E)
 <= B H [1+((E+1)^2-E^2)10^(-s m)]
 =  B H [1+(2E+1)10^(-s m)].                            (7.3)
```

**Proposition 7.1 (bounded-width latest layers).** Fix any natural number
`K>=0`. For every real `s` with `0<s<1`, every `m>=1`, every `Q0`, and every
endpoint

```text
m<=E<=m+K,                                               (7.4)
```

the exact local budget (7.3) holds with

```text
B_K:=2(K+1).                                             (7.5)
```

**Proof.** By (2.6), `a=E-m+1<=K+1`. Equation (7.2) gives
`L1_(m,E)<=2H(K+1)=B_K H`. Since `10^(-sm)>0`, the bracket in (7.3) is at
least one. This proves (7.3) with (7.5). The constant is independent of
`m,E,Q0`; it is even independent of `s`. QED.

This is a nontrivial uniform parameter strip, including the first active
latest layer `E=m` with constant `B_0=2`. It is only a level-zero local result
on `E-m<=K`; it supplies no all-start, all-length localized premise.

## 8. Explicit insufficiency of this route outside bounded width

Fix any `s` with `0<s<1` and take

```text
E=2m,   m->infinity.                                    (8.1)
```

Then (2.6) gives `a=m+1`, while the normalized level-zero local budget is

```text
G_(s,m,E):=1+(2E+1)10^(-sm)
           =1+(4m+1)10^(-sm)->1.                        (8.2)
```

Let `R_T4(m,E)` denote the right side of the strongest termwise majorant
(5.7). For all sufficiently large `m`, (5.8) and
`2(10^m-1)>=Q0` make every self-sum cap and every cross-sum cap exactly `H`.
All difference caps are nonnegative. Consequently, at `E=2m`,

```text
R_T4(m,2m)
 >=2Ha+2Ha+4H*binom(a,2)
 =2Ha(a+1).                                             (8.3)
```

The three terms retained here are respectively the diagonal, all self-sums,
and all `k_r+k_u` cross-sums. Thus even under the optimistic limiting
assignment that every difference cap costs zero, the upper bound delivered by
termwise T4 followed by Cauchy--Schwarz is at least

```text
sqrt(H R_T4(m,2m))>=H sqrt(2a(a+1)).                    (8.4)
```

Relative to the desired right-hand scale, this delivered majorant has ratio

```text
sqrt(H R_T4(m,2m))/[H G_(s,m,2m)]
 >=sqrt(2(m+1)(m+2))/[1+(4m+1)10^(-sm)]
 ->infinity.                                            (8.5)
```

Therefore no constant depending only on `s` can turn the actual majorant
(5.7) delivered by this termwise route into the all-endpoint local budget.
T16 supplies no fixed-pi evaluation by Section 6. Thus the route consisting
of exact expansion, termwise T4 absolute bounds, T16's weighted-GCD theorem,
and second-moment-to-L1 Cauchy--Schwarz is insufficient in the explicit
regime (8.1).

Again, (8.3)-(8.5) concern the size of the proved upper-bound expression.
They are not lower bounds on `M_(m,2m)` or `L1_(m,2m)` and do not disprove the
local budget itself. The obstruction is the combination of unresolved
off-diagonal fixed-pi cancellation and the second-moment-to-L1 square-root
loss, not a demonstrated resonance of pi.

## 9. One exact narrower aggregate incidence target

The next target should not restate the local L1 budget. For the exact signed
layer (4.4), define the normalized weighted near-incidence

```text
Inc_(m,E)
 := sum_(omega,omega' in Omega_(m,E), omega!=omega')
      min(1, 1/[2H ||(omega-omega')pi||_T]).              (9.1)
```

Under the explicit T4 premise, pi is irrational, so every denominator in
(9.1) is nonzero. The target is the following precise fixed-orbit statement:

```text
There exists C_inc>=0 such that, for every m>=1 and E>=m,
Inc_(m,E) <= C_inc (E-m+1).                              (T25-inc)
```

All pairs in (T25-inc) are ordered; the diagonal is excluded; both signs are
included; `H=10^m`; and the layer endpoint is exactly `E`. In particular,
(T25-inc) implies the critical-scale count

```text
#{(omega,omega') in Omega_(m,E)^2 :
    omega!=omega' and
    ||(omega-omega')pi||_T<1/(2H)}
 <= C_inc(E-m+1).                                       (9.2)
```

Conversely, (9.1) is stronger than only (9.2) because it records all dyadic
distance scales rather than just saturated returns.

By (5.1), (4.5), and the triangle inequality, (T25-inc) would give the exact
diagonal-scale second-moment estimate

```text
M_(m,E)<=H[2(E-m+1)+Inc_(m,E)]
        <=(2+C_inc)H(E-m+1),                             (9.3)
```

and hence

```text
L1_(m,E)<=H sqrt((2+C_inc)(E-m+1)).                      (9.4)
```

This is strictly narrower than the unresolved local budget: along `E=2m`,
(9.4) still has an unbounded `sqrt(m)` loss against (8.2). Thus
(T25-inc) is an honest aggregate incidence target isolating near-coincident
signed coefficient differences; it is not a disguised assertion of the
all-layer local budget and does not imply C1.

## 10. Terminal status and audit checklist

The following are partial conclusions, with their status explicit.

1. **Proved in this prose note:** the exact endpoint domain, both ordered
   orientations, the cosine identity (3.3), and the inclusive-frequency
   diagonal/off-diagonal identity (4.3).
2. **Conditional on T4's external premise:** the individual fixed-pi bound
   (5.5). The premise is not promoted to a kernel theorem here.
3. **Machine-checked imported arithmetic:** T16's constant `574913232`; it
   does not supply a fixed-pi estimate.
4. **Proved nontrivial uniform range:** for each fixed `K`, every latest layer
   with `m<=E<=m+K` satisfies the level-zero local budget with the explicit
   constant `2(K+1)`.
5. **Demonstrated method insufficiency:** along `E=2m`, the strongest bound
   obtained from this route has the divergent ratio (8.5). This is not a
   lower bound for the actual Fourier sum.
6. **Exact narrower unresolved target:** the weighted ordered incidence
   estimate (T25-inc).

No estimate for all endpoint layers or dyadic blocks is asserted, no fixed-pi
scale-matched L1 predicate is asserted, and no C1 verdict is asserted.
