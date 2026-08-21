# T54: signed residue-1/residue-9 primitive pairing

Status: `proof sketch`. The cited T12, T16, T24, T29, T31, T32, T34, and
T49 interfaces are machine-checked. Every new finite identity below is proved
in this note, but has not been formalized in Lean.

## 1. Source, normalized scope, and conclusion

The canonical local question has no external source URL. Its byte-exact text
is delivered as `CANONICAL_STATEMENT.txt`, with SHA-256

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

That question asks for an ordered long-lag collision estimate for the decimal
digits of pi, uniformly in all positive `m,N`. This note addresses only the
residual sparse-Fourier sibling A12 at `(mu,c)=(8,1)`. It does not prove T29's
width-weighted predicate at `Real.pi`, C2, C1, or the canonical collision
estimate.

The T52 note is unverified motivation, not a premise. We independently
reconstruct its residue-1 and residue-9 boxes and insert them into T49's exact
signed primitive contribution. The outcome is:

1. there is no phase-independent algebraic cancellation of these boxes;
2. no signed lower bound at `alpha=pi` is derived from their positive shell
   mass alone;
3. their orientation-completed quartic contribution factors exactly into ten
   products of two real bilinear correlations of one-dimensional lacunary
   exponential sums;
4. one explicit `O(L^3)` estimate for those products is the remaining
   lower-dimensional estimate for this box.

Residue 8 is not isolated: residues 1 and 9 have not been removed from the
full primitive sector.

### Quantifiers and possible ambiguities

Throughout Sections 3-8,

```text
Q0,t are arbitrary natural numbers,
L = 2^t,
m = 1,
N = 4L+1,
alpha = pi.
```

Thus `L>=1`, `m,N>=1`, and no constant may depend on the four selected
exponents. The word "residue" always means the residue modulo ten of the
positive primitive factor after the exact power `10^ell` has been removed.
It does not mean the residue of `d` itself when `ell>0`. "Orientation" has two
different meanings that will not be conflated:

- simultaneous reversal `J` produces another member of T49's positive
  record-pair domain with the same positive value;
- swapping the two records produces the negative off-diagonal difference and
  is restored by T49's outer factor `2`.

## 2. Kernel-checked interfaces used

Only the following machine-checked interfaces are used.

1. T12, `not_arithmeticExcluded_eight_one_at_one` and
   `mem_orderedLongPairDomain_eight_one_one_iff`: at `(8,1,m=1)`, independently
   of `Q0`, every ordered pair of unequal coordinates below `N` is an exact
   admissible record.
2. T16, `fourTokenSign`, `Noncancelling`, and
   `tenValuation_lowDecimalCoefficient`: the four labels have signs
   `(+,+,-,-)`, opposite signs may not share an exponent in the primitive
   sector, and a displayed lowest coefficient in `{1,2,8,9}` gives the exact
   decimal valuation.
3. T24, `canonicalDyadicPartition`: canonical blocks are constructed from the
   decreasing binary digits of `N-1` and are half-open endpoint blocks.
4. T29, `translatedCanonicalBlocks`, `widthWeight`, and
   `inclusiveFrequencies`: the block weight is literally
   `sqrt(finish^2-start^2)`, and the frequencies are `1<=h<=10^m`, inclusive.
5. T31, `blockPositiveDifferenceDomain`, `blockDifferenceValue`,
   `blockDifferenceExponent`, and `primitiveBlockDifferenceDomain`: a strict
   positive signed-frequency difference is represented by the four exponents

   ```text
   [orderedFirst(p.1), orderedSecond(p.2),
    orderedSecond(p.1), orderedFirst(p.2)]                  (2.1)
   ```

   with signs `(+,+,-,-)`.
6. T32, `blockRecordDomain` and `mem_blockRecordDomain_iff`: a record belongs
   to a block exactly when it is admissible and its frequency endpoint lies in
   the weak-left, strict-right interval.
7. T34, `inclusiveRealKernel` and
   `inclusiveRealKernel_frequency_audit`: this is the real part of T32's
   one-sided kernel on exactly the inclusive frequencies.
8. T49, `primitiveRecordDomain`,
   `mem_primitiveValuationStratum_iff`, and
   `primitiveSectorContribution`: the signed primitive sector is

   ```text
   P_prim(Q0;m,N;alpha)
    = 2 * sum_(B in translatedCanonicalBlocks N)
        sum_(p in primitiveRecordDomain 8 1 Q0 m N B)
          K_m(d(p),alpha) / w(B),                           (2.2)
   ```

   where `K_m=inclusiveRealKernel`. The outer `2` is the exact pair of swapped
   ordered off-diagonal orientations; it is not an absolute value.

The phase normalization comes from the imported machine-checked definition
`Theory.PiDigits.T27.phase`:

```text
phase(k,x) = exp(2*pi*i*k*x).                               (2.3)
```

Consequently

```text
K_m(d,alpha) = sum_(h=1)^(10^m) cos(2*pi*alpha*h*d).        (2.4)
```

At `m=1, alpha=pi`, zero frequency is absent and the endpoint `h=10` is
present:

```text
K_1(d,pi) = sum_(h=1)^10 cos(2*pi^2*h*d).                   (2.5)
```

## 3. The literal canonical block and weight

Since

```text
N-1 = 4L = 2^(t+2),                                        (3.1)
```

the binary expansion of `N-1` has the single bit `t+2`. T24's literal
recursion therefore gives

```text
translatedCanonicalBlocks N = [B],
B.start = 1,
B.level = t+2,
B.finish = 1+2^(t+2) = N.                                  (3.2)
```

Thus the unique block is the half-open endpoint interval `[1,N)`, and its
literal T29 weight is

```text
w = w(B)
  = sqrt(N^2-1)
  = sqrt(16L^2+8L),
4L < w < 4L+1 = N.                                         (3.3)
```

Both strict inequalities follow by squaring positive quantities.

Partition its integer endpoints into four inclusive intervals:

```text
I1 = {1,...,L},
I2 = {L+1,...,2L},
I3 = {2L+1,...,3L},
I4 = {3L+1,...,4L}.                                        (3.4)
```

Each has exactly `L` elements, and for `xj in Ij`,

```text
1 <= x1 < x2 < x3 < x4 <= 4L < N.                          (3.5)
```

## 4. Exact records and block membership

For unequal natural numbers `x,y<N`, define the literal T12 record

```text
R(x,y) = (true,  (x-y,y))  if y<x,
         (false, (y-x,x))  if x<y.                         (4.1)
```

Here a record is a Boolean paired with a `(lag,start)` pair of natural
numbers. Directly from the definitions,

```text
orderedFirst(R(x,y)) = x,
orderedSecond(R(x,y)) = y,
signedDecimalFrequency(R(x,y)) = 10^x-10^y,
frequencyEndpoint(R(x,y).2) = max(x,y).                    (4.2)
```

Its lag is `|x-y|>=1=m`. T12 removes the arithmetic exclusion for every `Q0`,
and (3.5) puts the endpoint in `[1,N)`. Hence T32's membership equivalence
proves

```text
R(x,y) in blockRecordDomain 8 1 Q0 1 B                    (4.3)
```

for every record used below. This checks the weak left endpoint `1`, strict
right endpoint `N`, positive lag, and arithmetic survival; no larger ambient
domain is substituted.

Reversing a record swaps its coordinates:

```text
rev(R(x,y)) = R(y,x),
signedDecimalFrequency(rev(q)) = -signedDecimalFrequency(q). (4.4)
```

For a positive record pair `p=(q+,q-)`, put

```text
J(p) = (rev(q-),rev(q+)).                                   (4.5)
```

Then `J` preserves block membership, strict positive orientation, and the
positive value `d(p)`. It is simultaneous reversal followed by the swap needed
to keep the positive-frequency record first.

## 5. Independent reconstruction of residues 1 and 9

Fix one quartet

```text
x = (x1,x2,x3,x4) in I1 x I2 x I3 x I4.                   (5.1)
```

Define the two positive integers

```text
d1(x) = 10^x4 + 10^x1 - 10^x2 - 10^x3,
d9(x) = 10^x4 + 10^x2 - 10^x1 - 10^x3.                    (5.2)
```

### 5.1 Positivity

Put

```text
U(x3,x4) = 10^x4-10^x3,
V(x1,x2) = 10^x2-10^x1.                                   (5.3)
```

Then

```text
d1 = U-V,
d9 = U+V.                                                  (5.4)
```

Since `x4>=x3+1`, `U>=9*10^x3`; since `x3>=x2+1`, this is at
least `90*10^x2`, whereas `0<V<10^x2`. Thus

```text
U>V>0,
d1>0,
d9>0.                                                      (5.5)
```

This proves the strict signed-frequency orientation required by T31/T49.

### 5.2 Literal T52-style injections

The two displayed record pairs are

```text
p1,00(x) = (R(x4,x2), R(x3,x1)),
p9,00(x) = (R(x4,x1), R(x3,x2)).                            (5.6)
```

By (4.2), their positive differences are respectively `d1(x)` and `d9(x)`.
Their four exponents are distinct, so no positive label shares an exponent
with a negative label. They therefore satisfy T16's exact `Noncancelling`
predicate and belong to T49's `primitiveRecordDomain`.

The unique lowest exponent of `d1` is `x1`, with coefficient `+1`. Factoring
out `10^x1` gives

```text
d1 = 10^x1 * (1+10*A1) for a unique A1 in Nat,
tenValuation(d1) = x1,
tenPrimitivePart(d1) == 1 (mod 10).                        (5.7)
```

Indeed the quotient has form `1+10Z` with integer `Z`; positivity forces
`Z>=0`. The unique lowest exponent of `d9` is also `x1`, now with coefficient
`-1`. Its positive quotient has form `-1+10Z`, forcing `Z>=1`, and hence

```text
d9 = 10^x1 * (9+10*A9) for a unique A9 in Nat,
tenValuation(d9) = x1,
tenPrimitivePart(d9) == 9 (mod 10).                        (5.8)
```

T16's `tenValuation_lowDecimalCoefficient` proves the displayed valuations.
To identify the primitive parts as well, apply T16's `ten_reduction` to
`d_r=10^x1*k_r`, where `k_1=1+10*A1` and `k_9=9+10*A9`. It gives
`10^x1*tenPrimitivePart(d_r)=10^x1*k_r`; cancellation of the positive natural
factor `10^x1` yields `tenPrimitivePart(d_r)=k_r`. Thus these are exactly
residue-1 and residue-9 primitive records, not merely integers congruent to 1
and 9 before removing powers of ten.
In both boxes the complete valuation range is therefore
`ell=x1 in {1,...,L}`; no valuation `0` or `ell>L` occurs in these selected
families.

Each map `x |-> p1,00(x)` and `x |-> p9,00(x)` is injective: (4.2) recovers
the four ordered coordinates from its two records. Hence each literal family
contains exactly `L^4` primitive record pairs.

The integer-value maps are also injective. To see this without assuming
unique signed decimal notation, move all negative powers to the other side.
Every coefficient is at most two and hence below ten, so ordinary uniqueness
of decimal digits applies without carries. The interval containing each
exponent then identifies `x1,x2,x3,x4`. The residue-1 and residue-9 value sets
are disjoint by (5.7)-(5.8).

### 5.3 Exact orientation-completed fibers

T52 displayed only (5.6). T49's primitive domain has four, not one,
representations of each selected value. They are as follows; the exponent
column is the literal vector (2.1).

| value | pair | records `(q+,q-)` | Bool pattern | exponent vector |
|---|---|---|---|---|
| `d1` | `p1,00` | `(R(x4,x2),R(x3,x1))` | `TT` | `[x4,x1,x2,x3]` |
| `d1` | `p1,01` | `(R(x4,x3),R(x2,x1))` | `TT` | `[x4,x1,x3,x2]` |
| `d1` | `p1,10` | `(R(x1,x2),R(x3,x4))` | `FF` | `[x1,x4,x2,x3]` |
| `d1` | `p1,11` | `(R(x1,x3),R(x2,x4))` | `FF` | `[x1,x4,x3,x2]` |
| `d9` | `p9,00` | `(R(x4,x1),R(x3,x2))` | `TT` | `[x4,x2,x1,x3]` |
| `d9` | `p9,01` | `(R(x4,x3),R(x1,x2))` | `TF` | `[x4,x2,x3,x1]` |
| `d9` | `p9,10` | `(R(x2,x1),R(x3,x4))` | `TF` | `[x2,x4,x1,x3]` |
| `d9` | `p9,11` | `(R(x2,x3),R(x1,x4))` | `FF` | `[x2,x4,x3,x1]` |

Equations (4.2) and (5.2) verify every value in the table. Every component is
in the exact block by (4.3), every difference is strictly positive by (5.5),
and every row is noncancelling because all four exponents are distinct.

The simultaneous reversal involution is exactly

```text
J(p_r,00)=p_r,11,
J(p_r,01)=p_r,10,       r in {1,9}.                         (5.9)
```

There are no further primitive record pairs with one of these values. Here is
a finite proof. If an unknown primitive pair has positive exponent multiset
`{u0,u1}`, negative exponent multiset `{u2,u3}`, and value `d_r(x)`, move its
negative powers and the selected positive powers to opposite sides. One gets
an equality of two sums of four powers of ten. At every exponent the
coefficient is in `{0,1,2,3,4}`, so repeated reduction modulo ten proves that
the exponent multisets on both sides are equal.

For completeness, fix an exponent `e`. Let `a_e,b_e in {0,1,2}` be its
multiplicities among the unknown positive and negative labels, and let
`c_e,d_e in {0,1}` indicate membership in the selected positive and negative
sets. Decimal uniqueness gives

```text
a_e+d_e = b_e+c_e.                                         (5.10a)
```

The selected positive and negative sets are disjoint, and `Noncancelling`
says that not both `a_e,b_e` are positive. If `c_e=1`, then `d_e=0` and
`a_e=b_e+1`; noncancellation forces `b_e=0,a_e=1`. If `d_e=1`, symmetrically
`a_e=0,b_e=1`. Outside both selected supports, (5.10a) gives `a_e=b_e`, so
noncancellation forces both to vanish. This coefficient-by-coefficient
argument also rules out equal-sign repetitions. Therefore

```text
{u0,u1} = the two selected positive exponents,
{u2,u3} = the two selected negative exponents.              (5.10)
```

The two independent label permutations give exactly the four rows displayed
for that value. T12's coordinate injectivity makes each resulting pair of
records unique. Thus each selected value has exactly four preimages in
`primitiveRecordDomain`, arranged in two `J`-orbits.

## 6. Exact signed orientation identity

Write

```text
chi_h(d) = cos(2*pi^2*h*d),       1<=h<=10.                 (6.1)
```

For one positive record pair of value `d`, swapping the two off-diagonal
records changes `d` to `-d`. T49's kernel identity is therefore

```text
phase(h,d*pi) + phase(-h,d*pi)
 = 2*chi_h(d).                                              (6.2)
```

After summing the inclusive frequencies, one positive pair contributes
`2*K_1(d,pi)/w` to (2.2). This is T49's outer factor `2`; no second swap factor
may be inserted.

For each quartet and each inclusive frequency, the literal residue pairing is

```text
chi_h(d1)+chi_h(d9)
 = cos(2*pi^2*h*(U-V)) + cos(2*pi^2*h*(U+V))
 = 2*cos(2*pi^2*h*U)*cos(2*pi^2*h*V).                       (6.3)
```

This is the elementary identity `cos(a-b)+cos(a+b)=2 cos(a) cos(b)`. Hence

```text
K_1(d1,pi)+K_1(d9,pi)
 = 2 * sum_(h=1)^10
       cos(2*pi^2*h*U) cos(2*pi^2*h*V).                    (6.4)
```

All signs are now visible:

- all four primitive representations of a fixed `d_r` have coefficient `+1`
  in T49's positive-difference sum;
- the swapped off-diagonal orientation is a complex conjugate and creates the
  positive real factor `2` in (6.2);
- the inspected interfaces provide no nonnegativity statement for the
  fixed-`pi` kernels or for the products in (6.4).

Thus the record orientations reinforce multiplicity; they do not cancel.

## 7. Finite pairing and lower-dimensional reduction

Define the two double sums

```text
A_h(L) = sum_(x3 in I3) sum_(x4 in I4)
           cos(2*pi^2*h*(10^x4-10^x3)),

B_h(L) = sum_(x1 in I1) sum_(x2 in I2)
           cos(2*pi^2*h*(10^x2-10^x1)).                    (7.1)
```

Because the quartet domain is the literal Cartesian product
`I1 x I2 x I3 x I4`, finite distributivity and (6.4) give the exact identity

```text
sum_(x in I1 x I2 x I3 x I4)
  (K_1(d1(x),pi)+K_1(d9(x),pi))
 = 2 * sum_(h=1)^10 A_h(L) B_h(L).                         (7.2)
```

There are two useful exact restricted contributions.

First, retain only the two literal T52-style pairs (5.6), but insert each into
T49's actual signed formula, including the swapped off-diagonal orientation:

```text
P_lit(L)
 = (2/w) * sum_x (K_1(d1(x),pi)+K_1(d9(x),pi))
 = (4/w) * sum_(h=1)^10 A_h(L)B_h(L).                      (7.3)
```

Second, retain the complete four-element primitive fiber over every selected
value. Using the exact multiplicity proved in Section 5.3,

```text
P_fib(L)
 = (2/w) * sum_x (4*K_1(d1(x),pi)+4*K_1(d9(x),pi))
 = (16/w) * sum_(h=1)^10 A_h(L)B_h(L).                     (7.4)
```

This factor `16` consists of `4` primitive representations, T49's factor `2`
for the swapped off-diagonal orientation, and the cosine-pairing factor `2`.

Let `F_box` be the disjoint union of all eight table rows over all quartets.
The exact finite partition of T49's actual primitive sector is

```text
P_prim(Q0;1,N;pi) = P_fib(L) + P_rest(L),                  (7.5)
```

where `P_rest` is the same signed sum (2.2) restricted to the finite complement
of `F_box` in `primitiveRecordDomain`. Equation (7.5) is an equality, not an
inequality. Since signed sums are not monotone, neither a bound nor a sign for
`P_fib` alone controls `P_prim`.

### One-dimensional exponential-sum form

For `j=1,2,3,4` and `1<=h<=10`, define

```text
S_j(h;L) = sum_(x in Ij) exp(2*pi^2*i*h*10^x).              (7.6)
```

Then

```text
A_h(L) = Re(S_4(h;L) * conjugate(S_3(h;L))),
B_h(L) = Re(S_2(h;L) * conjugate(S_1(h;L))).                (7.7)
```

Therefore the quartic box is exactly

```text
P_fib(L) = (16/w) * sum_(h=1)^10
  Re(S_4(h;L) conjugate(S_3(h;L)))
  Re(S_2(h;L) conjugate(S_1(h;L))).                         (7.8)
```

It is a product of real parts, not generally the real part of one product.
Equation (7.8) is the promised lower-dimensional reduction: each `S_j` is a
one-dimensional lacunary sum, and the frequency set has the ten literal
endpoints `1,...,10`.

## 8. The explicit remaining estimate and decision

The trivial bounds `|A_h|,|B_h|<=L^2` give only

```text
|P_fib(L)| <= (160/w)*L^4 < 40*L^3,                        (8.1)
```

one power larger than the fixed-`m` target scale `N^2`.

The single explicit lower-dimensional estimate isolated by this note is:

```text
There exists C_star>=0 such that, for every natural t, with L=2^t,

  | sum_(h=1)^10
      Re(S_4(h;L) conjugate(S_3(h;L)))
      Re(S_2(h;L) conjugate(S_1(h;L))) |
    <= C_star * L^3.                                       (E_box)
```

If `(E_box)` holds, then (3.3) and (7.8) give the fully explicit consequence

```text
|P_fib(L)| <= 4*C_star*L^2 <= (C_star/4)*N^2.              (8.2)
```

No interface inspected here proves `(E_box)`. It is not asserted as a theorem.
It is one lower-dimensional fixed-pi exponential-sum estimate, with all
parameters and endpoints explicit.

The decision for T54 is therefore a proved reduction, not a cancellation and
not a signed obstruction:

- T52's positive shell mass does not survive automatically as a signed lower
  bound, because no fixed-`pi` nonnegativity statement is available for the
  kernels in (7.8), and `P_rest` is present.
- Residues 1 and 9 do not cancel algebraically. Their exact pairing is the
  nonzero product identity (6.3); as an identity in a variable phase it is
  visibly not zero, for example at phase zero.
- Their complete selected fibers reduce exactly through (7.8) to the
  lower-dimensional sum on the left of `(E_box)`; the estimate `(E_box)`
  remains unproved.
- Residue 8 cannot be isolated, because no proved identity removes the
  residue-1 and residue-9 terms from the full primitive sector.

## 9. Skeptic's audit checklist

1. Source: `CANONICAL_STATEMENT.txt` has the displayed canonical hash and no
   external URL is invented.
2. Scope: only the A12 residual Fourier sibling at `(8,1)` is discussed.
3. Parameters: `Q0,t` are arbitrary naturals; `L=2^t`, `m=1`, `N=4L+1`, and
   `alpha=pi` are fixed before the four exponent choices.
4. Block: (3.1)-(3.3) reconstruct the entire canonical block list, half-open
   endpoints, and literal weight.
5. Records: (4.1)-(4.3) expose Bool orientation, lag, arithmetic survival,
   coordinates, signed frequency, and block endpoint.
6. Residues: (5.7)-(5.8) prove exact valuation and primitive residues 1 and 9.
7. Multiplicity: the table and (5.10) prove all four representations and no
   others over each selected value.
8. Orientations: (5.9), (6.2), and the explanation after (6.4) separate
   simultaneous reversal from swapped off-diagonal orientation.
9. Frequencies: (2.5) and (6.1) retain exactly `1<=h<=10`, including 10.
10. Finite identity: (7.2)-(7.5) give literal, fiber-completed, and complement
    decompositions with factors `4`, `16`, and no monotonicity step.
11. Endpoint: (7.8) proves the lower-dimensional reduction and `(E_box)`
    states the one remaining estimate with an explicit `L^3` scale.
12. Claim boundary: no primitive-sector bound, residue-8 reduction, T29, C2,
    C1, or canonical collision conclusion is claimed.
