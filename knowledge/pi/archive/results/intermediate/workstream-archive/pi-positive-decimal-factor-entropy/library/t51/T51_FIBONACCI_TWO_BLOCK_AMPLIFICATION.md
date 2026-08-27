# T51: a strictly non-semicircular Fibonacci coding with diluted decimal chains

Status: `proof sketch`, with an exact rational-arithmetic `experiment` and a
kernel-checked arithmetic companion.

Scope: **non-pi sibling only**. The real and orbit below are not pi. This note
has no implication for C1 and neither proves nor disproves positive decimal
factor entropy for pi.

The T45 and T50 notes were motivation only. No claim from either note is a
premise below. The coding, strict non-semicircle certificate, rotation limit,
decimal chain, and energy estimate are derived here. One literature theorem,
fourth-power-freeness of the Fibonacci word, is cited directly from its pinned
source in Section 7 rather than through T45.

## 1. Provenance, normalized statement, and ambiguities

The immutable canonical statement is copied byte-for-byte as
`pi-positive-decimal-factor-entropy.txt`. Its SHA-256 is

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

The original source URL is absent because the canonical question was
formulated locally. T51 studies a recorded sibling, not the canonical real.

Put

```text
alpha = (3-sqrt(5))/2,   beta = 1-alpha,   delta = 1-2*alpha.
```

Define the zero-indexed Fibonacci word by

```text
f_j = floor((j+2)*alpha)-floor((j+1)*alpha),   j >= 0.       (1.1)
```

At every position use the overlapping pair `f_j f_(j+1)`, with names

```text
A=00,   B=01,   C=10.                                      (1.2)
```

For an ordered injective digit coding `c`, define

```text
z_j = c(f_j f_(j+1)),
x_j = sum_(k>=0) z_(j+k)/10^(k+1),
e(t) = exp(2*pi*i*t),
S_M(h) = sum_(j=0)^(M-1) e(h*x_j).                          (1.3)
```

The potentially ambiguous conventions are fixed as follows.

1. The tuple `(a,b,c)` records the digits on `(A,B,C)` in that order.
2. The enumeration is Python's lexicographic
   `itertools.permutations(range(10),3)`; there is no symmetry quotient.
3. Pairs overlap. They are not disjoint pairs or substitution blocks.
4. Leading zeroes and every suffix are retained.
5. Closure is in `R/Z` after the series evaluation in (1.3).
6. A closed semicircle has length at most `1/2`, including its endpoints.
7. The Fejer band is signed and strict: `|h|<H`; it includes zero and both
   signs of every nonzero frequency.
8. Every limiting statement below is along the ordinary prefix length `M`,
   or along the explicitly stated subsequence `M=10^n`.

## 2. Fibonacci convention and rotation model

The word (1.1) begins `010010100100101...`. It is the fixed point beginning
in `0` of `sigma(0)=01`, `sigma(1)=0`: telescoping (1.1) puts the `k`-th one
at `floor(k/alpha)-1=floor(k*phi^2)-1` and the `k`-th zero at
`floor(k/(1-alpha))-1=floor(k*phi)-1`. In `sigma(f)`, the one following the
`k`-th zero is therefore at

```text
floor(k*phi)-1 + k = floor(k*phi^2)-1,
```

so `sigma(f)` and `f` have the same one positions. The nested fixed-point
prefixes identify the convention completely.

Images and image boundaries show that the exact length-two language is
`{00,01,10}`: `01` occurs inside `sigma(0)`, and boundaries give `10` or
`00`. All occur in `010010`. Thus (1.2) is exhaustive.

For `0<=t<1`, define

```text
W(t)_n = floor(t+(n+1)*alpha)-floor(t+n*alpha).              (2.1)
```

Then `f=W(alpha)` and

```text
shift^j(f) = W(frac((j+1)*alpha)).                           (2.2)
```

The forward orbit of an irrational rotation is dense and equidistributed.
For later use, the equidistribution statement follows directly from Weyl's
criterion: for every nonzero integer `m`, the average of
`e(m*(t+j*alpha))` is a geometric sum bounded independently of its length,
divided by that length, because `e(m*alpha) != 1`.

Testing the first two bits in (2.1) gives the exact pair cylinders

```text
A: 0 <= t < delta,
B: delta <= t < beta,
C: beta <= t < 1.                                          (2.3)
```

The endpoint words, obtained directly from the one-sided values of (2.1),
are

```text
0f, 001f, 010f, 01f, 10f, 1f.
```

If `Z=P(f)=BCABCBCA...` is the overlapping-pair word, applying the pair map
to those six words gives

```text
AZ, ABCZ, BCAZ, BCZ, CAZ, CZ.                              (2.4)
```

These identities are infinite identities, not finite-prefix observations.

## 3. Deterministic selection

For the cases preceding the selected coding, the lexicographic tuples are

```text
(0,1,2), (0,1,3), (0,1,4), (0,1,5), (0,1,6).              (3.1)
```

In all five cases `a<b<c`. Within one first-pair cylinder, the first later
pair disagreement must be `A=00` against `B=01`: the overlapping pairs agree
through their common first bit, and `11` never occurs. Since `a<b`, the exact
minimum and maximum endpoint words are therefore

| cylinder | minimum | maximum |
|---|---|---|
| `A` | `AZ` | `ABCZ` |
| `B` | `BCAZ` | `BCZ` |
| `C` | `CAZ` | `CZ` |

Density supplies both one-sided endpoints, while order intervals are closed,
so these are extrema over the complete symbolic suffix closure. Decimal
evaluation is strictly order preserving here: the largest digit in (3.1) is
at most `6`, so after a first digit difference the entire remaining tail can
cancel at most `6/9<1` times the leading unit difference.

Let `zeta=0.Z` after digit coding. The endpoint values are

```text
E(AZ)   = (a+zeta)/10,
E(ABCZ) = (100a+10b+c+zeta)/1000,
E(BCAZ) = (100b+10c+a+zeta)/1000,
E(BCZ)  = (10b+c+zeta)/100,
E(CAZ)  = (10c+a+zeta)/100,
E(CZ)   = (c+zeta)/10.                                    (3.2)
```

For `(a,b,c)=(0,1,d)` the three top-level circle gaps, in order from `A` to
`B`, `B` to `C`, and exterior `C` to `A`, are exactly

```text
9*(10+d)/1000,   (9*d-10)/100,   1-d/10.                  (3.3)
```

The common `zeta` cancels. Every other complementary component lies inside
one first-digit cylinder, whose diameter is at most `d/90`.

A compact circle set lies in a closed semicircle exactly when its complement
contains an open gap of length at least `1/2`. For `d=2,3,4,5`, the exterior
gap `1-d/10` is at least `1/2`, so the first four tuples in (3.1) are
contained. For `d=6`, the complete gap bounds are

```text
A->B:       18/125,
B->C:       11/25,
exterior:    2/5,
internal: <= 1/15.                                         (3.4)
```

Their maximum is `11/25`, strictly below `1/2` by `3/50`. Thus the
deterministically selected coding is

```text
A=00 -> 0,   B=01 -> 1,   C=10 -> 6.                       (3.5)
```

It is the lexicographically first strictly non-semicircular coding. The
checker independently enumerates all 720 tuples with exact `Fraction`
arithmetic, but only (3.1)-(3.4) are needed for firstness.

Continuity completes the closure argument: agreement through digit `N-1`
changes a decimal value by at most `10^(-N)`. The symbolic suffix closure is
compact, so its continuous decimal image is exactly the closure of the
decimal suffix orbit. No finite-prefix set or enlarged cover is substituted.

## 4. Limiting orbit average at `h=1`

Define the pair-digit step function for (3.5):

```text
q(t)=0 on [0,delta), q(t)=1 on [delta,beta),
q(t)=6 on [beta,1).                                        (4.1)
```

With arguments modulo one, put

```text
G(t)   = sum_(k>=0) q(t+k*alpha)/10^(k+1),
G_N(t) = sum_(k=0)^(N-1) q(t+k*alpha)/10^(k+1).             (4.2)
```

Equations (2.2)-(2.3) give `x_j=G(frac((j+1)*alpha))`.
Because every digit is at most `6`, uniformly in `t`,

```text
0 <= G(t)-G_N(t) <= 2/(3*10^N),
|e(h*G(t))-e(h*G_N(t))| <= 4*pi*|h|/(3*10^N).              (4.3)
```

Each `G_N` is a finite step function. Equidistribution from Section 2 applies
to its Riemann-integrable phase, and (4.3) permits `N` to tend to infinity on
both the orbit-average and integral sides. Therefore, for every integer `h`,

```text
A_h := lim_(M->infinity) S_M(h)/M
     = integral_[0,1] e(h*G(t)) dt.                         (4.4)
```

This proves existence; a finite orbit sample is not being used as evidence
for the limit.

For `N=2`, rotating the cylinders in (2.3) partitions the circle as

| interval | first two coded digits | length |
|---|---:|---:|
| `[0,delta)` | `01` | `delta` |
| `[delta,beta)` | `16` | `alpha` |
| `[beta,2-3*alpha)` | `60` | `delta` |
| `[2-3*alpha,1)` | `61` | `3*alpha-1` |

Hence

```text
J_2 = integral e(G_2(t)) dt
    = delta*e(.01) + alpha*e(.16) + delta*e(.60)
      + (3*alpha-1)*e(.61).                                (4.5)
```

The elementary bounds

```text
cos(pi/50)>9/10,  cos(8*pi/25)>1/2,
cos(6*pi/5)=-(1+sqrt(5))/4,  cos(61*pi/50)>=-1             (4.6)
```

give, after substituting `alpha` and `delta`,

```text
Re(J_2) > (24*sqrt(5)-53)/10.                              (4.7)
```

For completeness, the first inequality in (4.6) follows from
`cos u >= 1-u^2/2`; the second follows from `8*pi/25<pi/3`; the third is the
standard half-angle evaluation from the regular-pentagon identity; the last
is the universal lower bound for cosine.

The exact tail in (4.3) at `N=2` is at most `1/150`, so

```text
Re(A_1) > (24*sqrt(5)-53)/10 - pi/75.                      (4.8)
```

Both constants admit elementary rational certificates. First,
`(223/100)^2=49729/10000<5`, so `sqrt(5)>223/100`. Second,
Machin's identity

```text
pi/4 = 4*atan(1/5)-atan(1/239)
```

follows by applying the tangent addition formula twice:
`tan(2*atan(1/5))=5/12`, `tan(4*atan(1/5))=120/119`, and the
last subtraction has tangent one in the correct quadrant. Since
`0<atan u<u` for `u>0`, it gives `pi<16/5`. Substitution in (4.8) yields the
strict rational certificate

```text
Re(A_1) > 13/250 - 16/375 = 7/750 > 0.                    (4.9)
```

Thus the explicit nonzero frequency is `h=1`. This conclusion comes from the
integral calculation, not from non-semicircularity. Non-semicircular support
alone cannot force a Fourier coefficient: for example, equal mass on the
three cube roots of unity has non-semicircular support and zero first moment.

## 5. T40 decimal-frequency chains

The kernel-checked T40 module fixes

```text
decimalFrequency(h,r)=10^r*h,
DecimalFrequencyAdmissible(H,h,r) iff 10^r*|h|<H,
```

and proves the exact `2r` endpoint-loss pattern for the pi orbit. Its
pi-specific endpoint theorem is not applied to this sibling. Instead, the
same identity is proved directly from (1.3): multiplying `x_j` by `10^r`
removes its first `r` decimal digits modulo an integer, so

```text
e(10^r*h*x_j)=e(h*x_(j+r)).                                (5.1)
```

For `r<=M`, shifting the finite sum gives exactly

```text
S_M(10^r*h)
 = S_M(h) - sum_(j=0)^(r-1)e(h*x_j)
          + sum_(j=M)^(M+r-1)e(h*x_j),                     (5.2)
|S_M(10^r*h)-S_M(h)| <= 2r.                                (5.3)
```

The companion `T51DecimalChainRange.lean` imports T40 and kernel-checks the
complete full-band range. For every `n>=1`, with

```text
M=10^n, H=M/2, h=1,
```

it proves

```text
DecimalFrequencyAdmissible(H,1,r) iff r<n iff r<=n-1.      (5.4)
```

Indeed, throughout the displayed range
`10^r<=10^(n-1)=H/5<H`, while `r>=n` gives `10^r>=M>H`.
Also `r<=n-1<=M`, so every endpoint in (5.2) is valid.

Let `c0=7/750`. By (4.9), there is an integer `n0` such that for every
`n>=n0`,

```text
|S_(10^n)(1)| >= Re(S_(10^n)(1)) > c0*10^n.               (5.5)
```

Given any requested endpoint `R>=0`, choose `n` with

```text
n>=n0, n>=R+1, and 10^n >= 3000*R/7.                      (5.6)
```

Then every `0<=r<=R` is strictly admissible and (5.3)-(5.6) give

```text
|S_(10^n)(10^r)| > (7/1500)*10^n.                         (5.7)
```

This is an explicit arbitrarily long chain. Moreover, for every
`n>=max(n0,3)`, the complete maximal range `0<=r<=n-1` obeys (5.7), because
`10^n>=3000*(n-1)/7` at `n=3` and the inequality propagates after multiplying
the left side by ten.

## 6. Complete full-band Fejer energy

For positive integers `M,H`, define the complete strict-band energy

```text
E_H(M) = sum_(h in Z, |h|<H) (1-|h|/H)*|S_M(h)|^2.         (6.1)
```

The kernel-checked T10 theorem
`orderedPair_fejerKernel_eq_ordinaryFejerEnergy` verifies this convention for
an arbitrary finite real sequence. Directly expanding finite sums gives

```text
E_H(M)=sum_(0<=i,j<M) K_H(x_j-x_i),                        (6.2)
K_H(t)=(1/H)*(sin(pi*H*t)/sin(pi*t))^2.
```

The continuous value is `K_H(0)=H`. If
`rho=||t||_(R/Z)>0`, then `sin(pi*rho)>=2*rho` on `[0,1/2]`, hence

```text
0<=K_H(t)<=H,   K_H(t)<=1/(4*H*rho^2).                    (6.3)
```

The latter is also the inverse-square bound kernel-checked in T8.

## 7. Prefix multiplicity

The sole external combinatorial theorem used here is:

> The Fibonacci infinite word contains no fourth power.

This is Proposition 1, printed p. 201, PDF p. 4, of F. Mignosi and G. Pirillo,
*Repetitions in the Fibonacci infinite word*, RAIRO 26 (1992), 199-204,
DOI `10.1051/ita/1992260301991`. The retained PDF
`mignosi-pirillo-1992.pdf` has SHA-256
`96e3bca270ea1a52671670757e39b31be97ad1eec194d2321d241e5be253bfe1`.
The proposition attributes the result to Karhumaki. This citation is direct;
the T45 note is not a premise.

We now derive the exact consequence needed here. If equal coded factors of
length `ell` begin at `a<b`, put `d=b-a`. Injectivity of (3.5) recovers the
underlying `ell+1` binary symbols. If `3d<=ell+1`, equality at distance `d`
through those symbols makes the length-`4d` binary factor at `a` four copies
of its first length-`d` block, contradicting the cited theorem. Therefore

```text
3d>ell+1.                                                   (7.1)
```

Set

```text
D_ell=floor((ell+1)/3)+1,
L(M,ell)=ceil(M/D_ell).                                     (7.2)
```

Successive occurrences of one coded length-`ell` factor among starts
`0,...,M-1` are at least `D_ell` apart. If there are `q` occurrences, their
span is at least `(q-1)D_ell` and at most `M-1`, proving
`q<=L(M,ell)`.

## 8. Circular shells and the energy limit

Take

```text
M=10^n, H=M/2, ell=n,
D_n=floor((n+1)/3)+1, L_n=ceil(M/D_n).                     (8.1)
```

Let `P_i` be the integer represented by the first `n` coded digits of `x_i`,
including leading zeroes. Since every suffix lies in `[0,2/3]`,

```text
x_i=P_i/M+x_(i+n)/M.                                       (8.2)
```

For unequal labels let

```text
s=min(|P_i-P_j|, M-|P_i-P_j|)>=1.
```

The circle triangle inequality and (8.2) give

```text
||x_i-x_j|| >= (s-2/3)/M >= s/(3M).                       (8.3)
```

This modular ranking handles circle wraparound; ordinary left/right ranking
would be unsafe because the selected closure is not in a semicircle. For one
fixed `i` and one distance `s`, there are at most two residue labels, each
with at most `L_n` indices by Section 7. Thus the shell has at most `2L_n`
points.

Equal-prefix classes have sizes `q_gamma<=L_n`. By (6.3), their total ordered
pair contribution, including every diagonal pair, is at most

```text
H*sum_gamma q_gamma^2 <= H*L_n*sum_gamma q_gamma = L_n*M*H. (8.4)
```

For fixed `i`, unequal shell `s` contributes at most

```text
2*L_n/(4*H*(s/(3M))^2) = 9*L_n*M^2/(2*H*s^2).             (8.5)
```

The elementary telescoping comparison
`1/s^2<=1/(s*(s-1))` for `s>=2` gives
`sum_(s>=1)1/s^2<=2`. Summing (8.5), then over all `M` first indices, and
combining with (8.4), yields

```text
E_H(M) <= L_n*M*H + 9*L_n*M^3/H = 37*L_n*M*H,             (8.6)
```

where the last equality uses `H=M/2`. Therefore

```text
0 <= E_H(M)/(H*M^2)
   <= 37*L_n/M
   <= 37*(1/D_n+1/M)
   < 37*(3/(n+1)+10^(-n)).                                 (8.7)
```

The right side tends to zero. Hence the requested complete normalized
full-band limit is

```text
lim_(n->infinity) E_(10^n/2)(10^n)/((10^n/2)*10^(2n)) = 0. (8.8)
```

The chain does not contradict (8.8). Its positive and negative frequencies
number only `2n` in a band of width comparable to `M`; even replacing every
chain sum by its trivial maximum `M` gives normalized chain mass at most
`4n/M`. Conversely, (5.7) and the weight bound
`1-10^r/H>=4/5` give actual normalized chain mass at least
`4*c0^2*n/(5M)` for the maximal range. Both bounds tend to zero. The surviving
obstruction is **spectral dilution**, not fixed-frequency cancellation.

## 9. Replay and status

From a directory containing only the delivered artifacts, run

```text
./verify.sh
```

It hash-checks every retained input, recomputes the 720 exact geometry cases,
verifies that `(0,1,6)` is first, and checks the strict `3/50` and `7/750`
certificates. The finite `n=1,...,30` range checks are an `experiment`; the
universal range is the separately kernel-checked Lean theorem. From a checkout
of the pinned AllMath Lean project, replay that independent gate with

```text
./verify_lean.sh /path/to/AllMath
```

The script compiles the delivered file against the project's T40 module and
prints the axioms of both theorems. `lean_output.txt` records the replay from
this build; only `propext`, `Classical.choice`, and `Quot.sound` occur. The
Python checker verifies the exact algebra leading to the displayed phasor and
shell constants; the infinite equidistribution and kernel arguments remain
the prose proof, not a finite-computation claim.

The conclusions of this note remain a `proof sketch` until independent
review. The two range theorems in `T51DecimalChainRange.lean` are
`machine-checked` when the stated Lean replay succeeds. No T45 or T50 sketch
claim is promoted, and no claim about pi or C1 is made.
