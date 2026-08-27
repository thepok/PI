# T137: tensor limits of two-profile Lorenz meets

Date: 2026-08-12 UTC.

Claim label: `proof sketch`. The elementary arguments below are written for
direct checking, but this note has no kernel-checked formalization. The replay
is an `experiment`: it certifies the stated finite enumerations and direct
tensor calculations, not any universal theorem. The unbounded-family result
rests on the prose proof in Section 7, not on extrapolation from the replay.

## 1. Immutable statement, normalized scope, and ambiguities

The canonical problem has no external source URL; the program formulated it
on 2026-07-22. The delivered `canonical_statement.txt` is a byte-exact copy of
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`, with SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

The canonical question asks whether, for every integer `A>=1`, every
sufficiently large `n` admits an `N>=1` such that

```text
A*n*Q_pi(n,N) <= N^2,
```

where `Q_pi` counts ordered, diagonal-inclusive circle-distance near returns
of the first `N` points of the fixed decimal orbit of pi. T137 does not change
or answer those quantifiers. It studies a sibling finite-profile model.

The following choices remove the relevant ambiguities before deduction.

1. A profile is a finite nonincreasing vector of nonnegative integers, not
   identically zero. Trailing zeros are immaterial and are inserted when two
   widths must agree. Its mass is the sum of its coordinates.
2. Every pair `a,b` has equal positive mass. `E(a)=sum_i a_i^2` is the ordered,
   diagonal-inclusive collision energy of the associated histogram.
3. In the exhaustive sweep a profile is represented uniquely by its positive
   coordinates, hence by an integer partition. Pairs are unordered and
   self-pairs are included.
4. `a tensor b` is the sorted vector of all products `a_i*b_j`, with zeros
   retained to the declared ambient width during direct computations.
5. CRT realizability means realizability as the two marginal residue
   histograms of one integer multiset. It does not assert that the
   majorization meet is the joint histogram.
6. The tensor-coordinate cap is the ambient count before zero removal. Thus a
   width-three profile has `3^k` coordinates at power `k`.
7. No independence of residue coordinates, meet multiplicativity, or
   T135-style probabilistic transfer is assumed.

## 2. Lorenz order, meet, energy, and ratio

For a sorted equal-mass profile `x`, let

```text
L_x(j) = x_1 + ... + x_j
```

after zero-padding. Write `x prec y` when `L_x(j)<=L_y(j)` for every `j` and
the total masses agree. Thus `x` is the more diffuse profile. For two
equal-mass profiles define `c=a meet b` by

```text
L_c(j) = min(L_a(j),L_b(j)).                              (2.1)
```

The minimum of the two discrete concave Lorenz sequences is concave: if the
active minimum changed from `L_a` to `L_b` between adjacent indices, the
crossing inequalities and the decreasing increments of each sequence put the
new increment between the adjacent old increments. Equivalently, the
hypograph of a pointwise minimum is the intersection of the two convex
hypographs. Hence the increments in (2.1) are nonincreasing and define a
profile. They are integers for integer input. Equation (2.1) immediately says
that `c prec a,b`; any `x prec a,b` has `L_x<=min(L_a,L_b)=L_c`, so `x prec c`.
Thus `c` is the greatest common lower bound.

Define the scale-invariant candidate

```text
R(a,b) = min(E(a),E(b)) / E(a meet b).                    (2.2)
```

The denominator is positive because the common mass is positive. If
`x prec y`, the finite doubly-stochastic characterization gives `x=D y` after
zero-padding. Jensen applied in each row of `D`, followed by its column sums,
gives `sum x_i^2 <= sum y_i^2`. Consequently

```text
1 <= R(a,b).                                             (2.3)
```

## 3. Scaling invariance

**Proposition 3.1.** For every positive integer `t`,

```text
R(t*a,t*b)=R(a,b).
```

**Proof.** Every Lorenz sum is multiplied by `t`, and

```text
min(t*L_a(j),t*L_b(j))=t*min(L_a(j),L_b(j)).
```

Therefore `(t*a) meet (t*b)=t*(a meet b)`. Also
`E(t*x)=t^2 E(x)`. The common factor `t^2` cancels in (2.2). This proves the
claim. The same calculation works for every positive real scale when real
profiles are allowed. QED.

## 4. Exact CRT realizability

**Proposition 4.1.** Every two nonzero equal-mass integer profiles `a,b` are
exactly the sorted residue-mass profiles of one finite integer multiset modulo
two coprime moduli.

**Proof.** Let `a` have `r` positive entries, `b` have `s`, and both have mass
`N`. Choose coprime integers `q>=r` and `q'>=s`; the replay uses the explicit
choices

```text
q = the least positive power of 2 at least r,
q' = the least positive power of 3 at least s.           (4.1)
```

Make a row-label list containing `a_i` copies of `i`, and a column-label list
containing `b_j` copies of `j`. Both lists have length `N`, so pair them in
their listed order. For each pair `(i,j)`, let `u=q^(-1) mod q'` and set

```text
x_(i,j) = i + q*(((j-i)*u) mod q').                      (4.2)
```

Then `x_(i,j)=i mod q` and `x_(i,j)=j mod q'`. The multiset of the `N` values
in (4.2) therefore has row counts exactly `a` and column counts exactly `b`.
Unused residue classes contribute zeros; sorting recovers the original
profiles. If distinct integer representatives are wanted, add distinct
multiples of `q*q'` to repeated values. QED.

This proof realizes arbitrary integer transportation tables, including the
one produced by the paired lists. It does not identify the positive cell
masses of that table with `a meet b`. Such an identification would be a
separate and generally false assertion.

## 5. Unconditional tensor majorization

**Lemma 5.1.** If `x prec y` and `z` is a nonnegative profile, then
`x tensor z prec y tensor z`.

**Proof.** After zero-padding, write `x=D y` with `D` doubly stochastic. Then

```text
x tensor z = (D tensor I)(y tensor z).
```

`D tensor I` is doubly stochastic. Permuting either side into decreasing order
does not change majorization, proving the claim. QED.

**Proposition 5.2.** Put `c=a meet b` and

```text
W_k = (a tensor k) meet (b tensor k),                    (5.1)
```

where `tensor k` denotes the `k`-fold tensor power. For every integer `k>=1`,

```text
c tensor k prec W_k.                                     (5.2)
```

**Proof.** Since `c prec a`, tensor Lemma 5.1, iteration, and transitivity give
`c tensor k prec a tensor k`; similarly `c tensor k prec b tensor k`. It is
therefore a common lower bound of the two tensor powers. Their meet `W_k` is
the greatest common lower bound, which is exactly (5.2). QED.

Energy is multiplicative under tensor products:

```text
E(x tensor y)=sum_(i,j)(x_i*y_j)^2=E(x)E(y).              (5.3)
```

Applying square-energy monotonicity to (5.2) yields the unconditional bound

```text
E(c)^k <= E(W_k),
R(a tensor k,b tensor k) <= R(a,b)^k.                    (5.4)
```

This is deliberately an inequality, not meet multiplicativity. Its direction
does not by itself prove amplification.

## 6. Independent reconstruction of the T132 witness

The accepted T132 literature note is not imported as a proof premise. Starting
from its exact displayed label multiplicities

```text
(3,1,1,3,1,1) on labels 0,...,5,
```

direct squaring gives exact-label energy

```text
C=3^2+1^2+1^2+3^2+1^2+1^2=22.
```

Reduction modulo `2` has sorted profile `a=(5,5,0)` and energy `50`.
Reduction modulo `3` has sorted profile `b=(6,2,2)` and energy `44`. Their
Lorenz sums are respectively `(5,10,10)` and `(6,8,10)`, so (2.1) gives

```text
a meet b=(5,3,2),  E(a meet b)=25+9+4=38.
```

The average marginal energy is `(50+44)/2=47`. Thus the replay reconstructs
the strict chain entirely with integers:

```text
22 < 38 < 44 < 47.                                      (6.1)
```

CRT here identifies an actual joint residue tuple, but no product of marginal
probabilities is used.

The tempting identity

```text
(a meet b) tensor 2 = (a tensor 2) meet (b tensor 2)     (6.2)
```

is finitely falsified. Direct sorting and Lorenz minima give the right side

```text
(25,23,12,12,12,4,4,4,4),
```

with energy `1650`, whereas the left side has energy `38^2=1444`. This is
consistent with the unconditional direction (5.4). It proves (6.2) false but
says nothing universal about asymptotic ratios. The direct T132 tensor ratios
also increase from `k=2` to `k=3` and decrease from `k=3` to `k=4`, so the
replay falsifies monotonicity for that pair; finite nonmonotonicity is not an
asymptotic theorem.

## 7. A proved unbounded family

We first isolate the tensor estimate that replaces the false identity (6.2).
For `1<p<2`, write

```text
M_p(x)=sum_i x_i^p,   m=min(a_1,b_1).
```

**Lemma 7.1.** For `W_k` from (5.1),

```text
E(W_k) <= [m^(2-p) min(M_p(a),M_p(b))]^k.                (7.1)
```

**Proof.** The first Lorenz coordinate of a meet is the minimum of the first
coordinates, so `(W_k)_1=m^k`. Because `W_k prec a tensor k,b tensor k`, the
doubly-stochastic argument and Jensen for the convex function `t^p` give

```text
M_p(W_k) <= min(M_p(a tensor k),M_p(b tensor k))
          = min(M_p(a),M_p(b))^k.                        (7.2)
```

Every coordinate `w_i` of `W_k` is at most `m^k`. Therefore

```text
E(W_k) = sum_i w_i^(2-p) w_i^p
       <= (m^k)^(2-p) M_p(W_k),
```

which together with (7.2) is (7.1). QED.

Now take the integer profiles

```text
a=(4,1,1),  b=(3,3,0),  mass 6.                         (7.3)
```

Both have energy `18`. Use `p=3/2`. Then `m=3`,

```text
M_(3/2)(a)=4^(3/2)+1+1=10,
M_(3/2)(b)=2*3^(3/2)=6*sqrt(3)>10.                       (7.4)
```

For `A_k=a tensor k` and `B_k=b tensor k`, Lemma 7.1 gives

```text
E(A_k meet B_k) <= (10*sqrt(3))^k.
```

The numerator of `R(A_k,B_k)` is `18^k` by (5.3), hence

```text
R(A_k,B_k) >= (18/(10*sqrt(3)))^k
             = (3*sqrt(3)/5)^k.                         (7.5)
```

The square of the base is `27/25>1`. Thus (7.5) tends to infinity. Every
`A_k,B_k` is a nonzero equal-mass integer pair, and Proposition 4.1 realizes
it exactly by CRT. This proves that `R` has no universal finite ceiling on the
fixed two-profile domain.

No assertion about pi or an orbit enters this family.

## 8. Exhaustive finite experiment

Run from a directory containing only the four delivered files:

```text
python3 verify_t137.py > raw_output.txt
sha256sum canonical_statement.txt
```

The verifier uses Python integers and `Fraction`; it performs no floating-point
calculation. It refuses optimized Python because optimization removes
assertions. It recursively generates every decreasing positive partition of
each mass `1<=N<=24` with at most `12` parts. For every unordered pair,
including self-pairs, it:

1. computes both Lorenz arrays and their exact integer meet;
2. computes the numerator and denominator of `R` and compares ratios by
   integer cross-multiplication;
3. constructs (4.1)--(4.2) and checks both residue histograms exactly.

The declared sweep contains exactly `2,693,413` pairs. The bounded maximum is

```text
R=180/110=18/11
a=(13,1,1,1,1,1,1,1,1,1,1,1),
b=(8,8,8),
a meet b=(8,6,1,1,1,1,1,1,1,1,1,1).                   (8.1)
```

This is only an `experiment`. In particular, (8.1) does not prove a ceiling;
the universal conclusion comes instead from the family and proof in Section
7.

The verifier also directly recomputes both the T132 pair and (7.3) at every
tensor power satisfying the explicit ambient-coordinate cap

```text
3^k <= 100,000.
```

Thus the declared powers are exactly `1<=k<=10`; `3^10=59,049` is included
and `3^11=177,147` is excluded. At each power it sorts both tensor profiles,
forms the Lorenz meet, checks (5.2) from all partial sums, and recomputes all
energies. `raw_output.txt` records every numerator and denominator.

## 9. Scope boundary

`PI-MEET` is the separate assertion that suitable residue profiles of the
literal fixed-pi decimal orbit achieve the required meet-energy decay at every
sufficiently large depth. Nothing in arbitrary CRT realizability places the
constructed multiset on that prescribed orbit, and nothing in the unbounded
family supplies the required quantifiers. PI-MEET remains a `conjecture` and
is unproved.

The exact terminal scope markers are:

```text
PI-MEET_STATUS: conjecture; unproved
MEET_MULTIPLICATIVITY_ASSUMED: no
INDEPENDENCE_ASSUMED: no
FIXED_PI_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
VERDICT: PROVED UNBOUNDED FAMILY
```
