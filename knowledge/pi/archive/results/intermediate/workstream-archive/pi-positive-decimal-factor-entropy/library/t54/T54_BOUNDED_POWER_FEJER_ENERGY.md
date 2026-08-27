# T54: bounded powers force complete Fejer-energy dilution

Status: `proof sketch` pending independent review. This is a self-contained
candidate proof with numbered finite inequalities. No assertion from the T45
or T51 notes is used as a premise.

Scope: **non-pi sibling theorem only**. Nothing below concerns the digits of
pi, proves C1, proves C4, or supplies fixed-pi cancellation.

## 1. Provenance and normalized target

The immutable canonical question was formulated locally, so no original
source URL exists. A byte-exact copy is delivered as
`pi-positive-decimal-factor-entropy.txt`. Its SHA-256 is

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

That canonical question asks about positive decimal factor entropy of pi.
This note tests a reusable sibling claim instead: bounded powers plus an
injective finite-radius symbolic coding imply dilution of the *complete*
triangular Fejer energy of the coded decimal suffixes.

The conventions and potentially ambiguous quantifiers are as follows.

1. A power bound is one fixed integer `K >= 2`, independent of every later
   length. A word is `K`-power-free if it contains no factor `U^K` with `U`
   nonempty. Thus "bounded-power-free" means that such a `K` exists.
2. The source is a one-sided word `w=(w_j)_(j>=0)` over a finite alphabet
   `A`. Its one-sided shift is `T`, and
   `X=closure({T^j w:j>=0})` in `A^N`.
3. A radius-`r` coding means an anticipation-`r` local rule
   `phi:A^(r+1)->{0,...,9}` and the induced map
   `(Phi(x))_j=phi(x_j,...,x_(j+r))`. The phrase "injective sliding-block
   coding" means that `Phi:X->Phi(X)` is injective. It need not mean that the
   local rule `phi` is pointwise injective.
4. All coded factors overlap. Leading zeroes are retained. Multiplicity is
   among all starts `0,...,M-1`, even though the factor extends beyond `M`.
5. The coded word is `z=Phi(w)`. Its suffix values are the convergent series
   `x_j=sum_(t>=0) z_(j+t)/10^(t+1)`, not rounded finite decimals.
6. Circle distance is `rho(u)=min_(m in Z)|u-m|`.
7. For positive integers `M,H`, the frequency cutoff is signed and strict:
   `|h|<H`. It includes `h=0` and both signs of nonzero frequencies. Every
   ordered pair, including the diagonal, occurs on the kernel side.
8. The final `O(1/n)` means that explicit constants `C` and `N`, fixed after
   `K` and the coding are fixed, satisfy the bound for every integer `n>=N`.

No literature theorem is required. Compactness, the power argument, the
Fejer identity, and all estimates are proved below.

## 2. The theorem with explicit constants

### Theorem T54

Let `K>=2`, let `w in A^N` be `K`-power-free, and let `Phi:X->Phi(X)` be an
injective anticipation-`r` sliding-block code as fixed above. Then there is an
integer `q>=1` with the following recognition property:

```text
if y,y' in Phi(X) and y_0...y_(q-1)=y'_0...y'_(q-1),
then Phi^(-1)(y)_0=Phi^(-1)(y')_0.                    (2.1)
```

Fix any such `q`, and define

```text
B       := K+q-1,
gamma   := 2*10^(-B),
ell_n   := n-q+1                         (n>=q),
D_n     := floor(ell_n/(K-1))+1,
L_n(M)  := ceil(M/D_n).
```

For `n>=q`, put `M=10^n` and `H=M/2`. Define

```text
e(t)       := exp(2*pi*i*t),
S_M(h)     := sum_(j=0)^(M-1) e(h*x_j),
Energy_H(M):= sum_(h in Z, |h|<H)
                 (1-|h|/H)*|S_M(h)|^2.
```

Then the following finite inequality holds for every integer `n>=q`:

```text
Energy_H(M)/(H*M^2)
 <= (1+10^(2*B))
      *(1/(floor((n-q+1)/(K-1))+1)+10^(-n)).        (2.2)
```

In particular, with

```text
N := max(1,2*(q-1)),
C := (2*K-1)*(1+10^(2*B)),
```

the exact asymptotic quantifiers are

```text
for every integer n>=N,
Energy_(10^n/2)(10^n)/((10^n/2)*10^(2*n)) <= C/n.   (2.3)
```

Consequently the normalized complete energy is `O(1/n)` and tends to zero.

If the local rule itself is injective on the radius-`r` windows occurring in
`X`, one may take `q=1`. In that case the sharper all-length statement is

```text
for every integer n>=1,
Energy_(10^n/2)(10^n)/((10^n/2)*10^(2*n))
 <= (1+10^(2*K))
      *(1/(floor(n/(K-1))+1)+10^(-n))
 <= K*(1+10^(2*K))/n.                              (2.4)
```

## 3. Uniform finite recognition

First note that `X` is compact: it is a closed subset of the compact product
of the finite discrete space `A`. The map `Phi` is continuous. Because it is
an injection from compact `X` into a Hausdorff product space, it is a
homeomorphism from `X` onto the compact image `Y=Phi(X)`. Hence
`Psi=Phi^(-1):Y->X` is continuous.

Consider the coordinate function `f(y)=Psi(y)_0`, from `Y` to the finite
discrete set `A`. For every `y in Y`, continuity first gives a relative-open
neighborhood on which `f` is constant. A basic product neighborhood inside it
constrains only finitely many nonnegative coordinates. If `q_y` is one more
than the largest constrained coordinate, then the relative prefix cylinder
in `Y` determined by `y_0,...,y_(q_y-1)` is smaller than that neighborhood,
and `f` is constant on it. These relative prefix cylinders cover compact `Y`;
choose a finite subcover and let `q>=1` be at least all of their lengths.

If `y,y'` agree in their first `q` symbols, choose a subcover cylinder
containing `y`. Both words agree with that cylinder's defining prefix, so
`f(y)=f(y')`. This proves (2.1). Since `Phi` commutes with the one-sided shift,
so does `Psi` on `Y`. Applying (2.1) after `t` shifts gives the translated
recognition rule

```text
y_t...y_(t+q-1)=y'_t...y'_(t+q-1)
  ==> Psi(y)_t=Psi(y')_t.                              (3.1)
```

This argument also explains why global injectivity must be imposed on the
compact orbit closure, rather than merely asserted on the countable set of
actual shifts. Compactness is what makes one recognition length uniform.

## 4. Numbered finite-prefix inequalities

Fix integers `n>=q` and `M>=1`. Suppose equal coded length-`n` factors start
at `a<b`, and put `d=b-a`. Every length-`q` subfactor wholly inside those
equal factors is equal. By (3.1), the source factors of length
`ell_n=n-q+1` at `a` and `b` are equal:

```text
w_(a+t)=w_(a+d+t) for 0<=t<ell_n.                    (4.1)
```

If `(K-1)*d<=ell_n`, then for `0<=v<d` and `0<=s<K-1`,
the index `s*d+v` is below `ell_n`, and repeated use of (4.1) gives

```text
w_(a+v)=w_(a+d+v)=...=w_(a+(K-1)*d+v).
```

Thus the length-`K*d` source factor at `a` is the `K`-th power of its first
length-`d` block, contrary to `K`-power-freeness. Therefore distinct
occurrences of one coded length-`n` factor obey the strict recurrence bound

```text
(K-1)*d>ell_n,
d>=D_n=floor(ell_n/(K-1))+1.                         (4.2)
```

List the `s` occurrences of any fixed coded factor among starts
`0,...,M-1`. Consecutive starts differ by at least `D_n`, so their total span
is at least `(s-1)D_n` and at most `M-1`. Hence

```text
s<=floor((M-1)/D_n)+1=ceil(M/D_n)=L_n(M).             (4.3)
```

Equation (4.3) is the required finite-prefix multiplicity inequality. It is
not an infinite-language frequency assertion.

## 5. Explicit decimal suffix separation

There cannot be `B=K+q-1` consecutive equal coded digits. Indeed, if
`z_j,...,z_(j+B-1)` were all the digit `c`, then the `q`-blocks beginning at
`j,...,j+K-1` would all equal `c^q`. Rule (3.1) would make
`w_j,...,w_(j+K-1)` one repeated source letter, a forbidden `K`-th power.

In particular, among the first `B` digits of every suffix there is a nonzero
digit and there is a digit at most `8`. The first fact and the nonnegativity of
all later digits give the lower bound. For the upper bound, use
`sum_(t>=0)9/10^(t+1)=1`. Uniformly for every `j>=0`,

```text
10^(-B) <= x_j <= 1-10^(-B),
|x_i-x_j| <= 1-2*10^(-B)=1-gamma.                    (5.1)
```

This also rules out terminating-zero and eventual-nine ambiguities for every
suffix. The separation is derived from power-freeness; it is not an extra
hypothesis about the digit set.

Now specialize to `M=10^n`. Let `P_i` be the integer represented by the first
`n` coded digits at start `i`, including leading zeroes. Splitting the series
after those digits gives the exact identity

```text
x_i=P_i/M+x_(i+n)/M.                                  (5.2)
```

For unequal prefix labels define their circular residue distance

```text
s(i,j)=min(|P_i-P_j|,M-|P_i-P_j|),
1<=s(i,j)<=M/2.                                       (5.3)
```

Write `k=P_i-P_j` and `delta=x_(i+n)-x_(j+n)`. For every integer `m`,

```text
|k+delta-m*M| >= |k-m*M|-|delta|.
```

Taking the minimum over `m`, then using (5.1), yields

```text
rho(x_i-x_j)
 >= (s(i,j)-(1-gamma))/M
 >= gamma*s(i,j)/M.                                   (5.4)
```

The last inequality is exactly
`(1-gamma)(s(i,j)-1)>=0`. Thus (5.4) is valid also for adjacent decimal
prefixes and for labels separated across the circular cut at `0`; no linear
ordering or semicircle assumption is hidden here.

For fixed `i` and fixed integer `s` in (5.3), at most two residue labels have
circular distance `s` from `P_i` (only one when `s=M/2`). Each label is one
coded length-`n` factor, so (4.3) gives the shell count

```text
|{j:0<=j<M and s(i,j)=s}| <= 2*L_n(M).                (5.5)
```

## 6. Fejer identity and pointwise bounds

Define the strict triangular kernel

```text
F_H(t)=sum_(h in Z, |h|<H)(1-|h|/H)*e(h*t).
```

Expanding the square of a finite geometric sum and grouping the `H^2`
ordered pairs by their difference gives, for every real `t`,

```text
F_H(t)=(1/H)*|sum_(u=0)^(H-1)e(u*t)|^2.               (6.1)
```

This proves directly that `0<=F_H(t)<=H`. If `rho(t)>0`, the geometric-sum
formula and periodicity give

```text
F_H(t)=(1/H)*(sin(pi*H*t)/sin(pi*t))^2
       <=1/(H*sin(pi*rho(t))^2)
       <=1/(4*H*rho(t)^2).                            (6.2)
```

The last step uses the chord bound `sin(pi*u)>=2u` for `0<=u<=1/2`.

Expanding `|S_M(h)|^2`, interchanging only finite sums, and applying (6.1)
proves the exact ordered-pair identity

```text
Energy_H(M)=sum_(0<=i,j<M) F_H(x_i-x_j).               (6.3)
```

No Fourier or kernel identity from T7, T45, or T51 is being imported.

## 7. Numbered Fejer-shell inequalities

Partition the pairs in (6.3) according to whether `P_i=P_j`. If the
multiplicity of label `P` is `m_P`, then (4.3) says `m_P<=L_n(M)` and
`sum_P m_P=M`. The bound `F_H<=H` therefore gives

```text
equal-prefix contribution
 <= H*sum_P m_P^2
 <= H*L_n(M)*sum_P m_P
 = H*M*L_n(M).                                        (7.1)
```

Fix `i` and an unequal shell `s`. Combining (5.4), (5.5), and (6.2) gives

```text
shell contribution for this i and s
 <= 2*L_n(M)/(4*H*(gamma*s/M)^2)
 = L_n(M)*M^2/(2*H*gamma^2*s^2).                      (7.2)
```

The elementary telescoping comparison

```text
sum_(s>=1) 1/s^2
 <= 1+sum_(s>=2) 1/(s*(s-1))
 =2                                                        (7.3)
```

shows that summing (7.2) over all nonempty shells for fixed `i`, and then all
`M` choices of `i`, gives

```text
unequal-prefix contribution
 <= L_n(M)*M^3/(H*gamma^2).                            (7.4)
```

Combining (7.1) and (7.4) proves the general finite shell estimate

```text
Energy_H(M)
 <= H*M*L_n(M)+L_n(M)*M^3/(H*gamma^2).                (7.5)
```

At the agenda parameters `M=10^n` and `H=M/2`, one has

```text
(M^3/(H*gamma^2))/(H*M)=4/gamma^2=10^(2*B).
```

Thus (7.5) becomes

```text
Energy_H(M) <= (1+10^(2*B))*H*M*L_n(M).               (7.6)
```

Finally, `ceil(M/D_n)<=M/D_n+1` gives the fully explicit normalized bound

```text
Energy_H(M)/(H*M^2)
 <= (1+10^(2*B))*L_n(M)/M
 <= (1+10^(2*B))*(1/D_n+1/M),                         (7.7)
```

which is exactly (2.2).

## 8. Exact asymptotic quantifiers

Let `N=max(1,2*(q-1))`. Then `n>=N` implies both `n>=q` and

```text
ell_n=n-q+1>=n/2.
```

Since `D_n>ell_n/(K-1)`, and since `10^n>=n` for every `n>=1`, (7.7) gives

```text
1/D_n < (K-1)/ell_n <= 2*(K-1)/n,
10^(-n) <= 1/n.                                      (8.1)
```

Substitution in (7.7) proves, for every integer `n>=N`,

```text
Energy_(10^n/2)(10^n)/((10^n/2)*10^(2*n))
 <= (2*K-1)*(1+10^(2*(K+q-1)))/n.                    (8.2)
```

This is (2.3) with the advertised explicit `C`. The right side tends to zero,
so the normalized energy does also.

When the local rule is pointwise injective on occurring windows, equality of
one coded digit recovers the source anchor symbol, so `q=1`. Then
`ell_n=n`, `B=K`, and `1/D_n<(K-1)/n`; using the second inequality in (8.1)
gives the sharper constant in (2.4).

## 9. What was and was not established

The reusable implication is valid under the standard convention that the
sliding-block map is injective on the compact one-sided orbit closure. The
proof isolates its two mechanisms:

1. finite inverse recognition transfers close recurrences of coded factors
   back to forbidden source powers, producing the multiplicity bound (4.3);
2. the same recognition excludes long endpoint-digit runs, producing the
   suffix gap (5.1) needed at the strict circular cut.

If "injective" were weakened to mean injective only on the countable set
`{T^j w:j>=0}`, the compactness proof of one uniform `q` would no longer
apply. The exact additional condition needed by this proof is uniform finite
recognizability (2.1). No assertion is made here that orbit-only injectivity
alone implies the energy estimate.

This note makes no claim about pi, C1, C4, or cancellation at any fixed-pi
frequency. The T45 and T51 notes motivated the question but supplied no
load-bearing statement.

## 10. Mechanical replay boundary

From a directory containing only the delivered files, run

```text
sh ./verify.sh
```

The script verifies the byte-exact canonical statement and the retained note
hash. This is file-integrity replay only. The universal inequalities are the
self-contained symbolic proof above, not an extrapolation from finite
computation.
