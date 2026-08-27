# T37: a same-start counterfamily to a linear four-row shell bound

Status: `proof sketch`.

This note imports the machine-checked T36 interface as input and treats only
the supercritical same-start and mixed rows of its literal weighted shell
incidence.  It gives an explicit infinite family on which the same-start rows
alone have order at least `N^2`.  Thus canonical-block localization does not
give a uniform `O(N)` estimate for the four-row sector.  The family is at
`m=1`, where the `N^2 10^(-s m)` term is also of order `N^2`; consequently it
does **not** refute `ARI_super`, `ARI_cancel`, C2, or C1.

All new conclusions in this note have status `proof sketch`.  Statements
explicitly identified as imported from T12, T24, T29, T32, T34, or T36 are
`machine-checked` in the accumulated library.

## 1. Provenance, scope, and quantifiers

The canonical local problem is retained byte-for-byte as
`CANONICAL_STATEMENT.txt`.  It has no external source URL and has SHA-256

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3.
```

That problem asks for one constant `C_s` for every `0<s<1`, uniformly over
all positive integers `m,N`, in the ordered long-lag collision estimate

```text
R_pi(m,N) <= C_s [N+N^2 10^(-s m)].                       (1.1)
```

T37 does not estimate `R_pi`.  It concerns the residual sparse-Fourier sibling
A12 and, within that sibling, only four of T34's six cancelling rows.

The binding quantifiers here are as follows.  Fix arbitrary natural-number
onsets `Q0,Qstar`.  For every positive `m,N`, T36 defines a supercritical
weighted shell incidence.  We ask whether the contribution of rows 2, 4, 5,
and 6 is at most `C(Q0,Qstar) N` for every positive `m,N`.  The counterfamily
below proves, at proof-sketch level, that no such constant exists.  It is
stronger in this respect than merely finding one unfavorable `N`.

No ambiguity is resolved by changing any convention: blocks remain half-open,
frequencies remain inclusive, and all arithmetic-survival filters remain in
the row domains.

## 2. Kernel-checked input

The principal imported file is

```text
TheoryLib.PiLongLagBlockCollisionDecay.T36T36SubcriticalCancellationSaving
```

with retained source SHA-256

```text
3ba4c206ba517179b3561210acf37d704ec8d73a70155b23e55174c27ac0fc24.
```

It imports T34 and has passed the kernel gate with only the standard allowed
axioms.  The exact interfaces used here are:

1. T24/T29: `translatedCanonicalBlocks N` is the canonical dyadic list
   partitioning `[1,N)`, and
   `widthWeight B=sqrt(B.finish^2-B.start^2)`.
2. T32: `blockRecordDomain 8 1 Q0 m B` retains both Bool orientations,
   positive lag, lag at least `m`, the literal arithmetic-survival predicate,
   and endpoint in `[B.start,B.finish)`.
3. T34: the six `cancellingRowDomain` definitions, the outer
   `repunitParameterDomain`, the exact coefficient `cancellingValue`, and the
   endpoint-pinned shells.
4. T12: `not_arithmeticExcluded_eight_one_at_one`, which says that at `m=1`
   the `(mu,c)=(8,1)` arithmetic exclusion is impossible for every `Q0`, start,
   and positive lag.
5. T36: `Supercritical`, `restrictedWeightedShellIncidence`,
   `sourceExponent_shell_endpoint_audit`, and
   `shellWeight_eq_shellIndex`.

T36's external irrationality-measure source is Zeilberger--Zudilin,
*The Irrationality Measure of Pi is at most 7.103205334137...*, DOI
`10.2140/moscow.2020.9.407`; the retained PDF hash recorded by T36 is
`3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
The counterfamily below does not use the published estimate or assume
`PublishedEstimate36Fifths Qstar`; `Qstar` is used only as the literal onset
appearing in T36's supercritical filter.

## 3. Exact common definitions

For `v,rho` in the natural numbers, write

```text
k=v+rho,
d(v,rho)=10^v(10^rho-1).                                  (3.1)
```

T34's exact outer domain is

```text
D_N={(v,rho): v<N, rho<N, 0<rho, v+rho<N}.                (3.2)
```

The apparently redundant individual bounds in (3.2) are retained because
they occur literally through the product of two `range N` finsets.

T36's exact supercritical filter at `(m,Qstar)` is

```text
Qstar <= d(v,rho)  and  5m < 31(v+rho).                   (3.3)
```

For an oriented record with start `n` and endpoint `E`, T34 uses

```text
recordOfStartEndpoint(epsilon,n,E)
  =(epsilon,(E-n,n)).                                      (3.4)
```

Natural subtraction in (3.4) is not treated as integer subtraction by fiat:
membership in T32's record domain enforces positive lag and the inequalities
used below.

For a canonical block `B`, put

```text
Q_B=blockRecordDomain 8 1 Q0 m B,
w_B=sqrt(B.finish^2-B.start^2).                            (3.5)
```

Literal membership is

```text
(epsilon,(ell,n)) in Q_B
iff 0<ell, m<=ell,
    not ArithmeticExcluded 8 1 Q0 m n ell,
    B.start<=n+ell<B.finish.                               (3.6)
```

Both orientations occur with coefficient one.  No arithmetic-survival clause
is dropped from an exact row count.

## 4. The four literal row domains

Let `C_(B,r)(v,rho,z)` denote T34's
`cancellingRowDomain 8 1 Q0 m B r v rho z`.  It is a filtered singleton: its
cardinality is one exactly when `rho>0` and both displayed records belong to
`Q_B`, and zero otherwise.

The target rows are exactly:

```text
row 2, positiveSameStart:
  (record(true,z,v), record(true,z,k));

row 4, negativeSameStart:
  (record(false,z,k), record(false,z,v));

row 5, mixedFirstEndpoint:
  (record(false,z,k), record(true,v,z));

row 6, mixedSecondEndpoint:
  (record(false,v,z), record(true,z,k)).                   (4.1)
```

Together with (3.6), their exact nonempty conditions can be read as follows.

```text
rows 2 and 4:
  z+m<=v<k;
  v and k both lie in [B.start,B.finish);
  the LongPairCore values (v-z,z) and (k-z,z) both survive;

rows 5 and 6:
  v+m<=z and z+m<=k;
  z and k both lie in [B.start,B.finish);
  the LongPairCore values (z-v,v) and (k-z,z) both survive. (4.2)
```

The pairs in (4.2) are in Lean's literal `(lag,start)` order.

Thus rows 2 and 4 have both residual endpoints `v,k` in one canonical block.
Rows 5 and 6 have both residual endpoints `z,k` in one canonical block.  The
mixed interval in (4.2) is empty unless `rho>=2m`.  These are consequences of
the literal domains, not replacements for them.

Define the exact four-row multiplicity

```text
M_B^4(v,rho)
 =sum_(z in range N) sum_(r in {2,4,5,6})
    #C_(B,r)(v,rho,z).                                     (4.3)
```

This retains every hidden exponent and row multiplicity.  Rows 1 and 3 are
absent, rather than estimated and discarded.

## 5. Exact shells, weights, and four-row incidence

For `x` real, T34 uses

```text
delta(x)=|x-round(x)|,
K_m=clog_2(10^m)-1.                                       (5.1)
```

The exact shells are

```text
S_0(m)={x: 0<=delta(x)<=10^(-m)},

S_j(m)={x: 2^(j-1)/10^m<delta(x)
             <=min(2^j/10^m,1/2)}, 1<=j<=K_m.             (5.2)
```

In particular, equality at `10^(-m)` belongs to shell zero.  Positive shells
are open below and closed above, including the cap at `1/2`.  T34's canonical
shell index assigns every real number to exactly one shell.

Set

```text
theta_m(d)=1                  if d*pi is in S_0(m),
theta_m(d)=2^(-j)             if d*pi is in S_j(m), j>=1. (5.3)
```

For every `0<=j<=K_m`, define the literal row-restricted shell incidence

```text
I_j^4(Q0,Qstar;m,N)
 =sum_(B in translatedCanonicalBlocks N)
   sum_((v,rho) in D_N; (3.3))
     if InDyadicShell m j (d(v,rho)*pi)
     then M_B^4(v,rho)/w_B else 0.                         (5.4)
```

The requested weighted sum is exactly

```text
A_4(Q0,Qstar;m,N)
 =I_0^4(Q0,Qstar;m,N)
   +sum_(j=1)^K_m 2^(-j) I_j^4(Q0,Qstar;m,N)
 =sum_(B in translatedCanonicalBlocks N)
   sum_((v,rho) in D_N; (3.3))
     [M_B^4(v,rho)/w_B] theta_m(d(v,rho)).                 (5.5)
```

The second equality in (5.5) is only an exchange of finite sums plus the
unique shell assignment.  Formulas (5.4)-(5.5) preserve T36's coefficient,
supercritical filter, block list, width, shell endpoints, and all positive
`m,N` ranges.  Every summand is nonnegative, and `A_4` is a literal
subincidence of T36's `supercriticalIncidence`.

The proposed localization conclusion would be

```text
there exists C=C(Q0,Qstar)>=0 such that
A_4(Q0,Qstar;m,N)<=C N for every m,N>=1.                  (5.6)
```

No claim that this proposed bound holds is made.

## 6. Explicit one-block family

Fix an integer `J>=2` and put

```text
L=2^(J-2),  M=4L=2^J,  m=1,  N=M+1=4L+1.                (6.1)
```

Because `N-1=2^J` has one nonzero binary digit, T24's exact canonical
partition consists of the single block

```text
B=[1,N),  B.start=1,  B.finish=N,  B.level=J.             (6.2)
```

Its literal weight is

```text
w_B=sqrt(N^2-1)<N.                                        (6.3)
```

Choose independently

```text
v in [L,2L),
k in [3L,4L),
z in [0,L),
rho=k-v.                                                   (6.4)
```

Each interval contains exactly `L` integers.  The inequalities in (6.4) give

```text
0<rho<N, v<N, k=v+rho<N,
z+1<=v<k,
v,k in [1,N).                                              (6.5)
```

Hence `(v,rho)` lies in the exact domain (3.2), and the lag requirements for
rows 2 and 4 in (4.2) hold at `m=1`.

At `m=1`, T12's machine-checked
`not_arithmeticExcluded_eight_one_at_one` applies to both positive lags
`v-z` and `k-z`.  Both records therefore survive for every value of `Q0`.
Their endpoints `v,k` lie in the unique block.  Consequently each choice in
(6.4) contributes one row-2 singleton and one row-4 singleton to (4.3).

There are exactly

```text
2 L^3                                                       (6.6)
```

such same-start row witnesses.  This is a multiplicity count: different `z`
values are deliberately retained even when they produce the same
`d(v,rho)`.

The supercritical height condition is automatic:

```text
5m=5<31k                                                    (6.7)
```

because `k>=3L>=3`.  Moreover

```text
d(v,rho)=10^v(10^rho-1)>=9*10^L.                          (6.8)
```

For every fixed `Qstar`, all sufficiently large `J` therefore satisfy the
literal onset `Qstar<=d(v,rho)` simultaneously for every selected pair.

## 7. Uniform lower shell coefficient at m=1

The shell depth is exactly

```text
K_1=clog_2(10)-1=4-1=3.                                  (7.1)
```

By T36's `shellWeight_eq_shellIndex`, every real argument has coefficient
`1` in shell zero or `2^(-j)` for some `1<=j<=3`.  Therefore, with all endpoint
conventions in (5.2) retained,

```text
theta_1(d)>=2^(-3)=1/8                                    (7.2)
```

for every positive integer `d`.  This lower bound is independent of the
actual distribution of `{d*pi}` and remains true at every shell boundary.

## 8. Quadratic lower bound and failure of O(N)

For every sufficiently large `J` such that `9*10^L>=Qstar`, as justified by
(6.8), insert the `2L^3`
same-start witnesses from (6.6) into the nonnegative exact sum (5.5).  Using
(6.3) and (7.2) gives

```text
A_4(Q0,Qstar;1,4L+1)
 >= (2L^3/w_B)(1/8)
  = L^3/(4w_B)
  > L^3/(4N).                                              (8.1)
```

Since `N=4L+1<=5L`, division by `N` yields the explicit unbounded ratio

```text
A_4(Q0,Qstar;1,4L+1)/N
 > L^3/(4N^2)
 >= L/100.                                                 (8.2)
```

Thus, given any real `C>=0`, choose a power of two `L=2^(J-2)` large enough
that

```text
L>100C  and  9*10^L>=Qstar.                               (8.3)
```

Equations (8.1)-(8.3) then give

```text
A_4(Q0,Qstar;1,4L+1)>C(4L+1).                             (8.4)
```

This refutes the proposed linear bound for every fixed pair `Q0,Qstar`.
Canonical-block
localization is therefore false as a route to a uniform `O(N)` bound for the
four rows: the exact responsible sector is already rows 2 and 4, the two
same-start rows.  No estimate of rows 5 and 6 is needed for the refutation,
although their literal domains and same-block restrictions were retained in
Sections 4-5.

## 9. What the counterfamily does not prove

At `m=1`, T36's `ARI_superAt` target is

```text
C_s [N+N^2 10^(-s)],                                      (9.1)
```

which is of order `N^2`.  The lower bound (8.1) is therefore compatible with
the literal `ARI_super(36/5)` predicate.  It refutes only the stronger proposed
linear estimate for the four-row sector.

Accordingly:

1. `ARI_super` is not asserted or refuted.
2. `ARI_cancel`, T29's all-scale square-function premise, C2, and C1 are not
   asserted or refuted.
3. No claim is made about the common-endpoint rows 1 and 3.
4. The external irrationality-measure estimate is not used.
5. No finite experiment is offered as proof of a universal statement.

## 10. Terminal conclusion

**Proof-sketch conclusion.**  For every fixed natural `Q0,Qstar`, the explicit
infinite family

```text
m=1,
N=2^J+1,
J>=2 and sufficiently large,
v in [2^(J-2),2^(J-1)),
v+rho in [3*2^(J-2),2^J),
z in [0,2^(J-2))                                          (10.1)
```

lies in T36's literal supercritical filter and contributes through its exact
same-start row domains, canonical block, width, and shells.  Its four-row
weighted incidence satisfies

```text
A_4(Q0,Qstar;1,N)/N>2^(J-2)/100 -> infinity.              (10.2)
```

Hence there is no uniform `O(N)` weighted-shell bound for the supercritical
same-start and mixed-row contribution.  The obstruction is specifically the
same-start hidden-exponent multiplicity inside one large canonical block;
merely knowing that both residual endpoints lie in that block is
quantitatively insufficient.

## 11. Verification map

- Imported machine-checked interfaces: T12, T24, T29, T32, T34, and T36.
- New result: the explicit counterfamily (10.1)-(10.2), status `proof sketch`.
- Lean declarations introduced: none.
- Literature claim introduced: none.
- Independent statement review: pending.
- Independent proof review: pending.
- Novelty or attribution claim: none.
