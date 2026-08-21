# T58: triangular Fejer route to the sparse short sector

Status: `machine-checked` for the five declarations listed in Section 11;
`proof sketch` for the analytic audit below; `experiment` for the replayed
finite instances. Final verdict: **INSUFFICIENT**. This artifact does not assert
C7, C2, C1, or any new property of the digits of pi.

## 1. Source, normalized task, and ambiguities

The canonical question is locally formulated and has no original source URL.
The byte-exact source is `pi-positive-decimal-factor-entropy.txt`, with SHA-256

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

It asks whether one fixed `eta>0` gives
`p_pi(n) >= 10^(eta*n)` for every sufficiently large `n`. T58 does not answer
that question. It audits one route to the explicit kernel-checked predicate
`DecimalFactorComplexity.T56LagSectorAudit.SparseShortRepunitIncidenceBound`.

The following quantifier and endpoint choices are fixed throughout.

1. `n` is a natural number and all eventual statements have `n>=N>=1`.
2. `L_n := 10^(n/2)`, where `/` is natural-number division.
3. `H_n := 10^n/2`. For `n>=1`, kernel-checked T27/T26 gives
   `2*H_n=10^n`, so `10^(-n)=1/(2H_n)` exactly.
4. The short rectangle is

   ```text
   R_n := {(r,j): 0<r<n and 0<=j<L_n-r}.             (1.1)
   ```

   Thus `r=n` and `j=L_n-r` are excluded.
5. The positive Fejer frequencies are exactly `1<=h<H_n`; `h=H_n` is
   excluded. Frequency zero is the constant term, and negative frequencies
   are restored by twice the real part.
6. Every near-return cutoff is strict:
   `rho(10^j(10^r-1)*pi)<10^(-n)`.
7. The T56 residual mask remains present. For fixed real `mu,c` and natural
   `Q0`, put

   ```text
   eps_n(r,j) = 1 if not ArithmeticExcluded(mu,c,Q0,n,j,r),
                0 otherwise.                         (1.2)
   ```

8. A phase-average statement means integration over a variable
   `alpha in [0,1)`. It is not a statement at the fixed phase `alpha=pi`.

## 2. Imported kernel-checked boundary

`T58TriangularFejerAudit.lean` imports T56 rather than restating its
definitions. The relevant machine-checked interfaces are:

| Module and declaration | Exact role |
|---|---|
| T56 `mem_sparse_short_sector_iff` | `0<r<n` and `r<L_n` |
| T56 `sparseShortRepunitIncidenceBound_iff_quantifiers` | exact target quantifiers |
| T56 `sparse_sector_linear_bounds_imply_QBound` | short and long linear bounds plus effective irrationality imply `Q_pi=O(L_n)` |
| T56 `sparse_sector_linear_bounds_imply_C7` | conditional bridge through T27 |
| T27 `two_mul_sparse_longBandwidth` | `2H_n=10^n` for `n>=1` |
| T27 `ordinaryFejerEnergy_eq_complete_triangular_band` | complete signed strict band and weights |
| T27 `C7_quantifiers_iff_Q_linear_quantifiers` | equivalence of two unproved fixed-pi predicates |
| sparse T26 `piSparseNearReturn_fejerKernel_lower` | strict central-kernel lower bound `4H_n/pi^2` |
| lower-density T26 `shortResidualPairCount` | twice the masked count over (1.1) |

No theorem in this table asserts its fixed-pi premise. The T56 prose note is
unverified and is not used as a premise.

## 3. Frequencies, weights, and exact Fejer identity

For `(r,j) in R_n` and `1<=h<H_n`, define

```text
q_(j,r)       := 10^j*(10^r-1),
Phi_n(h,j,r)  := h*q_(j,r),
w_n(h)        := 1-h/H_n.                            (3.1)
```

The subscript `n` on `Phi_n` records the ranges; its integer value depends
only on `(h,j,r)`. The weights satisfy `0<w_n(h)<1`. With
`e(x):=exp(2*pi*i*x)`, the order-`H_n-1` Fejer kernel is exactly

```text
K_(H_n-1)(x)
 = sum_(|h|<H_n) (1-|h|/H_n)e(hx)
 = 1 + 2 Re sum_(1<=h<H_n) w_n(h)e(hx).              (3.2)
```

Consequently the complete masked rectangle sum is

```text
F_n(pi)
 := sum_((r,j) in R_n) eps_n(r,j)
      K_(H_n-1)(pi*q_(j,r))

  = |X_n| + 2 Re B_n(pi),                            (3.3)

X_n := {(r,j) in R_n: eps_n(r,j)=1},

B_n(alpha)
 := sum_((r,j) in X_n) sum_(1<=h<H_n)
      w_n(h)e(alpha*Phi_n(h,j,r)).                   (3.4)
```

Every endpoint in (3.2)-(3.4) is strict. In particular there is no term at
`h=H_n`, and the zero mode is the displayed `|X_n|`.

## 4. Injectivity of `(j,r)` at fixed `h`

Fix `h>0` and positive lags `r_1,r_2`. Suppose

```text
Phi_n(h,j_1,r_1)=Phi_n(h,j_2,r_2).                   (4.1)
```

Cancel `h`. The remaining equality is

```text
10^j_1*(10^r_1-1)=10^j_2*(10^r_2-1).               (4.2)
```

Because every positive repunit factor `10^r-1` ends in `9`, its maximal
power-of-ten divisor is `1`. Taking the composite-base `10`-adic valuation in
(4.2) gives `j_1=j_2`. Cancelling the positive common power of ten gives
`10^r_1-1=10^r_2-1`, hence `r_1=r_2` by strict monotonicity of `10^r`.

The theorem `phi_fixed_h_injective` machine-checks this argument using the
composite-base reduction from the adjacent long-lag T16 module. It does not
use a prime-valuation multiplicativity theorem.

## 5. Complete collision classification

For positive `h`, write uniquely

```text
h = 10^a*u,
a = tenValuation(h),
u = tenPrimitivePart(h),
10 does not divide u.                                (5.1)
```

Let `A_r:=10^r-1`. Since `A_r` is coprime to `10`, so is every divisor of
`A_r`. Applying (5.1) to both multipliers gives the exact criterion

```text
Phi_n(h_1,j_1,r_1)=Phi_n(h_2,j_2,r_2)

iff

a_1+j_1 = a_2+j_2
and
u_1*A_(r_1) = u_2*A_(r_2).                           (5.2)
```

Proof of the forward direction: both sides are
`10^(a_i+j_i)*(u_i*A_(r_i))`. The parenthesized factors are not divisible by
`10`, because `A_(r_i)` is coprime to `10`; uniqueness of maximal powers of
ten gives the exponent equality, then cancellation gives the primitive
equality. The reverse direction is immediate by multiplication.

For a divisor-level parametrization, set

```text
g := gcd(A_(r_1),A_(r_2))
   = 10^gcd(r_1,r_2)-1.                              (5.3)
```

The standard identity in (5.3) follows by applying the Euclidean algorithm
to `gcd(10^a-1,10^b-1)`; replacing `a` by `a mod b` preserves the gcd, and
the terminal exponent is `gcd(a,b)`. Write `A_(r_1)=gA'` and
`A_(r_2)=gB'`, where `gcd(A',B')=1`. Euclid's lemma then gives the complete
parametrization

```text
u_1 = t*B',
u_2 = t*A'                                             (5.4)
```

for one positive integer `t`. Conversely (5.4), together with
`a_1+j_1=a_2+j_2`, gives a collision. Thus (5.2)-(5.4) classify all
collisions; no assumption that `(h,j,r)` itself is injective is made.

The machine-checked theorem `phi_collision_after_ten_reduction` verifies the
exact pre-cancellation equality underlying (5.2). The replay checks both
(5.2) and (5.4) on all fibers at `n=2,3`.

## 6. Explicit multiplicity bound

Fix an integer frequency `Q>0` and consider all legal representations

```text
Q=Phi_n(h,j,r),
1<=h<H_n, 0<r<n, 0<=j<L_n-r.                        (6.1)
```

Map a representation to `(r,a)`, where `a=tenValuation(h)`. This map is
injective on the fiber over `Q`:

1. Equal `r` and equal `a`, together with (5.2), give equal `j`.
2. The primitive equality in (5.2) then gives equal `u`.
3. Equation (5.1) gives equal `h`.

There are `n-1` choices for `r`. Moreover `h<H_n<10^n`, so
`10^a<=h<10^n` and therefore `0<=a<n`, giving at most `n` choices for `a`.
Hence every frequency fiber has the explicit uniform bound

```text
mult_n(Q) <= n*(n-1).                                (6.2)
```

This is intentionally conservative. It is sufficient for the audit and does
not pretend to exploit the simultaneous bounds on `t`, `j`, and `u`.

## 7. Exact variable-phase second moment

Let

```text
I_n := {(h,r,j): 1<=h<H_n and (r,j) in X_n}.
```

Orthogonality of distinct integer characters on `[0,1)` gives

```text
integral_[0,1) |B_n(alpha)|^2 d alpha
 = sum_(p in I_n) sum_(q in I_n)
     1_(Phi_n(p)=Phi_n(q)) w_n(h_p)w_n(h_q).          (7.1)
```

Separating `p=q` from `p!=q` yields the exact expansion

```text
D_n + O_n,                                           (7.2)

D_n = |X_n| * sum_(1<=h<H_n) w_n(h)^2,

O_n = sum_(p,q in I_n; p!=q; Phi_n(p)=Phi_n(q))
        w_n(h_p)w_n(h_q).                            (7.3)
```

There is no factor `1/2`: ordered off-diagonal pairs occur in both orders.
The machine-checked generic theorem
`collisionSecondMoment_eq_diagonal_add_offDiagonal` verifies this exact
ordered expansion. By (6.2) and `0<w_n(h)<1`, one obtains the coarse average
bound

```text
integral_[0,1) |B_n(alpha)|^2 d alpha
 <= n*(n-1)*|I_n|.                                   (7.4)
```

This is a variable-phase mean square. Equations (7.1)-(7.4) contain no
evaluation at `alpha=pi`.

## 8. Fejer reduction to one fixed-pi estimate

Let `A_n` be the number of masked strict near returns:

```text
A_n := |{(r,j) in X_n:
  rho(10^j*(10^r-1)*pi)<10^(-n)}|.                  (8.1)
```

By definition of lower-density T26's ordered short count,

```text
shortResidualPairCount(mu,c,Q0,n,L_n)=2*A_n.         (8.2)
```

For every member of (8.1), sparse T26's central Fejer bound and
`10^(-n)=1/(2H_n)` give

```text
4H_n/pi^2 <= K_(H_n-1)(pi*q_(j,r)).                 (8.3)
```

The specialization is exact: `(r,j) in R_n` makes `(j,j+r)` a legal ordered
pair below `L_n`. Its orbit difference differs from
`(10^(j+r)-10^j)*pi=q_(j,r)*pi` by an integer. Each character in (3.2), and
hence the Fejer kernel, is invariant under such an integer shift. Thus T26's
kernel bound at the orbit difference is precisely (8.3), not merely a
circle-distance comparison.

The Fejer kernel is nonnegative at every other point. Summing (8.3), then
using (3.3), gives the exact sufficient inequality

```text
shortResidualPairCount(mu,c,Q0,n,L_n)
 <= pi^2/(2H_n) * (|X_n|+2 Re B_n(pi)).              (8.4)
```

Thus the route leaves exactly the following fixed-pi estimate.

### Fixed-pi masked bilinear Fejer estimate `(F_pi)`

For the fixed parameters `mu,c in R` and `Q0 in N`, there exist real `D>0`
and natural `N>=1` such that, for every natural `n>=N`, with
`L_n=10^(n/2)` and `H_n=10^n/2`, one has

```text
1/(H_n*L_n) *
[
 sum_(0<r<n) sum_(0<=j<L_n-r)
   1_(not ArithmeticExcluded(mu,c,Q0,n,j,r))
   {
     1 + 2 Re sum_(1<=h<H_n)
       (1-h/H_n)
       exp(2*pi*i*pi*h*10^j*(10^r-1))
   }
] <= D.                                               (F_pi)
```

Empty sums have value zero, and every quotient and normalization in `(F_pi)`
is in the reals. The ranges are literally half-open: `0<r<n`, `j<L_n-r`, and
`h<H_n`. The normalization is exactly `H_n*L_n`, and the phase is the fixed
real number `pi`, not a variable or almost-everywhere phase. The term
"bilinear" groups `(r,j)` as one rectangle variable and `h` as the other.

Combining `(F_pi)` with (8.4) gives

```text
shortResidualPairCount(mu,c,Q0,n,L_n)
 <= (pi^2*D/2)*L_n.                                  (8.5)
```

Therefore `(F_pi)` proves T56's
`SparseShortRepunitIncidenceBound(mu,c,Q0)` with constant `pi^2*D/2` and the
same cutoff `N`. This implication is conditional: `(F_pi)` is not proved.

## 9. Staged-interface comparison

Only named, kernel-checked interfaces were compared.

1. **T56.** Its exact sector partition identifies the target but retains only
   the unconditional `2L_n*n` short bound. It supplies no `(F_pi)` instance.
2. **T27.** It proves that T56's eventual linear `Q_pi` bound and C7 are
   equivalent hypotheses, with explicit constants. It does not prove either
   hypothesis and has no fixed-phase rectangle evaluation theorem.
3. **Long-lag T12.** `ScaleMatchedL1Bound` and
   `ScaleMatchedSquaredEnergyBound` are explicit unproved premises for a
   different long residual domain. Their conditional consequences do not
   imply `(F_pi)` for `0<r<n`.
4. **Long-lag T16.** Its composite-base `tenValuation`,
   `tenPrimitivePart`, and `cancellationValue_ten_reduction` justify the
   arithmetic reduction used in Sections 4-6. They contain no analytic
   estimate at `pi`.
5. **Entropy T16.** Its microscopic occupancy comparisons concern strict
   pair counts and conditional full-entropy consequences. They do not bound
   the masked bilinear expression in `(F_pi)`.
6. **Sparse T26.** It supplies the exact strict Fejer band and central lower
   bound used in (8.3), but its C7 predicate is explicitly unproved.
7. **Lower-density T26.** It supplies the exact short rectangle and only the
   universal `2L_n*n` estimate.
8. **T31.** Its finite periodic transfer requires an explicit
   `PhaseApproximation` and `PeriodicModelBounds`. It constructs neither for
   the fixed decimal orbit of pi and therefore does not imply `(F_pi)`.

No T5 or T15 literature corpus was reopened.

## 10. Replay-checked abstract obstruction

Distinct integer frequencies and their phase average do not by themselves
bound one prescribed phase. For `m>=1`, take distinct frequencies
`k=1,...,m`, triangular weights

```text
v_k := 1-k/(m+1),                                    (10.1)
```

and phase-adapted coefficients `c_k:=v_k*e(-k*pi)`. Define

```text
P_m(alpha):=sum_(k=1)^m c_k e(k*alpha).              (10.2)
```

Orthogonality gives the exact phase average

```text
integral_[0,1) |P_m(alpha)|^2 d alpha
 = sum_(k=1)^m v_k^2
 = m*(2m+1)/(6*(m+1)).                               (10.3)
```

At the prescribed phase `alpha=pi`, every phase cancels its coefficient:

```text
|P_m(pi)|^2 = (sum_(k=1)^m v_k)^2 = m^2/4.           (10.4)
```

The ratio of (10.4) to (10.3) is
`3m(m+1)/(2(2m+1))`, which diverges linearly. This family is abstract and its
coefficients are adapted to the evaluation phase. It does not model the exact
positive coefficients in (3.4), and it is not evidence that `(F_pi)` fails.
It proves the narrower logical point required here: distinct base frequencies
and an averaged orthogonality bound alone cannot yield a uniform estimate at
one fixed phase.

Replay command from a directory containing only the delivered artifacts:

```sh
python3 t58_replay.py --write replay.json
cmp replay.json replay_expected.json
```

The script uses exact rational arithmetic for (10.3)-(10.4), checks all
frequency fibers and the exact diagonal/off-diagonal expansion at `n=2,3`,
and labels those finite checks `experiment` rather than proof.

## 11. Verdict and machine-checked map

**INSUFFICIENT.** Injectivity of `(j,r)`, the complete collision
classification, the bound `mult_n(Q)<=n(n-1)`, and the variable-phase second
moment do not control `B_n(pi)`. None of the named staged interfaces supplies
the one estimate `(F_pi)`. If `(F_pi)` were proved, (8.4)-(8.5) would establish
T56's existing short-sector predicate with uniform eventual constants.

This verdict asserts neither `(F_pi)` nor its negation, and it asserts none of
C7, C2, or C1.

Public machine-checked declarations:

```text
DecimalFactorComplexity.T58TriangularFejerAudit.mem_positiveFejerFrequencies_iff
DecimalFactorComplexity.T58TriangularFejerAudit.mem_shortRectangle_iff
DecimalFactorComplexity.T58TriangularFejerAudit.phi_fixed_h_injective
DecimalFactorComplexity.T58TriangularFejerAudit.phi_collision_after_ten_reduction
DecimalFactorComplexity.T58TriangularFejerAudit.collisionSecondMoment_eq_diagonal_add_offDiagonal
```

Pinned internal source hashes:

```text
41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc  T56LagSectorAudit.lean
e4e7b2dd5d080616edee252e05c50c3cc9f56ddc7cd0420b71c3acaca2710c65  T27SparseMicroscopicEquivalence.lean
bcb6ada3167623b8f3d5ce65bb4d10337526424fe13bb36511f4b7267a2bab9f  T16MicroscopicFullEntropy.lean
8f61cdce1f5cab84c58777274f019c124c872e42180c7a13123900883fe710f0  T26SparseLongBandFejer.lean
25d511ceacce66b3f1d87dc8b2a95fcc154e58dcc78095418da2a9a79ab1971e  T31DominantPeriodicTransfer.lean
a4108ff862c13ee0f9fa3fc877723856eb34497430cde36d85f7943ce0347bcf  T12ScaleMatchedSpectralFrontier.lean
4c73188eae8b457403b25ef0577d22a7c4446c539bcf72df60905bf084204aec  T16FiniteWeightedGCD.lean
744731fcaa2e252a8f63b0a0bbaf09ea86bdc72f379616437cc5b570f282e6b0  T26LongLagResidualReduction.lean
```
