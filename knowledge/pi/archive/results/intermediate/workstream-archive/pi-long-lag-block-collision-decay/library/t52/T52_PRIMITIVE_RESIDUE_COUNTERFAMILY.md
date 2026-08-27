# T52: exact primitive residues and a counterfamily to T49's incidence predicate

Status: `proof sketch`. The definitions and named theorems cited from T12,
T16, T29, T31, T34, T36, and T49 are machine-checked. The new finite
classification and counterfamily below are proved in prose and have not been
formalized in Lean.

## 1. Scope, source, and conclusion

The canonical local question has no external source URL. Its byte-exact text is
delivered as `CANONICAL_STATEMENT.txt`; its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3.
```

That question asks for the canonical ordered long-lag collision estimate. T52
does not address that estimate directly. It audits only T49's residual A12
sibling at `(mu,c)=(8,1)`. Throughout, `Q0` is an arbitrary fixed natural
number. No C2 or C1 claim is made.

The outcome is a counterfamily. The proposed arithmetic residues are correct:
the exact primitive record domain is the disjoint union of residues `1`, `8`,
and `9`, and residue `2` is empty. The proposed analytic designation of
residue `8` as the only exceptional sector is false. At `m=1`, each of the
residue-`1` and residue-`9` sectors alone violates T49's target-scale incidence
bound by an unbounded factor. Consequently

```text
PrimitiveIncidence 8 1 Q0
```

is false for every `Q0`. Section 4 independently re-proves the
frequency-dependent residue-`8` cross-valuation calculation suggested by the
unverified T47 note; it is not used as a premise. That calculation does not
define a stratum of T49's exact incidence predicate because the predicate
contains no frequency `h`.

## 2. Exact T49 input

Fix positive natural numbers `m,N`, a canonical block

```text
B = [B.start,B.finish) in translatedCanonicalBlocks N,
```

and write

```text
w(B) = sqrt((B.finish)^2-(B.start)^2).                       (2.1)
```

This is the literal T29 `widthWeight`; it is not replaced by block length.
T49's `mem_primitiveValuationStratum_iff` says that a pair `p=(q+,q-)`
belongs to its primitive record domain in `B` exactly when

```text
q+,q- are in blockRecordDomain 8 1 Q0 m B,
signedDecimalFrequency(q-) < signedDecimalFrequency(q+),
Noncancelling (+,+,-,-) (blockDifferenceExponent p).        (2.2)
```

Put

```text
a0 = orderedFirst(q+),       a1 = orderedSecond(q-),
a2 = orderedSecond(q+),      a3 = orderedFirst(q-).          (2.3)
```

T31's exact positive-value interface gives

```text
d(p) = blockDifferenceValue(p)
     = 10^a0 + 10^a1 - 10^a2 - 10^a3 > 0.                  (2.4)
```

Every `ai` is less than `N`. T49's direct finite regrouping theorem gives

```text
I_prim(Q0;m,N)
 = primitiveWeightedShellIncidence 8 1 Q0 m N
 = sum_(B in translatedCanonicalBlocks N) 1/w(B)
     * sum_(p in primitiveRecordDomain 8 1 Q0 m N B)
         W_m(d(p)*pi),                                      (2.5)
```

where T34's exact shell weight is

```text
W_m(x)
 = 1_[0 <= delta(x) <= 10^(-m)]
   + sum_(j=1)^K 2^(-j)
       1_[2^(j-1)/10^m < delta(x)
           <= min(2^j/10^m,1/2)],                          (2.6)

delta(x) = |x-round(x)|,
K = shellDepth(m) = clog_2(10^m)-1.                        (2.7)
```

The shell-zero upper endpoint is closed. Every positive-shell lower endpoint
is open and its upper endpoint is closed. The last upper endpoint retains the
cap `1/2`. T36's machine-checked endpoint audit states, for every `m>=1`,

```text
1 <= K,       10^m <= 2^(K+1),       2^K < 10^m.           (2.8)
```

Equation (2.5) is a sum over positive record differences only. T31's factor
of two for the reverse off-diagonal orientation occurs later in T49's sector
envelope; it is not part of `I_prim` and is not inserted here.

T49's fixed-constant target is

```text
I_prim(Q0;m,N) <= C * (N + N^2*10^(-s*m))                  (2.9)
```

for one `C>=0` after `s` and before all positive `m,N`.

## 3. Exhaustive primitive residue partition

Let

```text
ell(p) = min(a0,a1,a2,a3).                                 (3.1)
```

At least one token occurs at `ell`. Noncancellation in (2.2) says that all
tokens occurring there have the same sign. There are exactly two positive and
two negative labels, so the signed coefficient of `10^ell` is one of

```text
+1, +2, -1, -2.                                             (3.2)
```

The `+2` case is impossible. It would force `a0=a1=ell`; noncancellation
would then force `a2,a3>=ell+1`, and (2.4) would imply

```text
d(p) <= 2*10^ell - 2*10^(ell+1) = -18*10^ell < 0,          (3.3)
```

contradicting positivity.

All terms above `ell` are divisible by `10^(ell+1)`. Hence, for an integer
`Z`, the remaining cases have the following unique natural forms:

```text
lowest coefficient  +1:  d=10^ell*(1+10*Z),       Z>=0;
lowest coefficient  -2:  d=10^ell*(8+10*(Z-1)),   Z>=1;
lowest coefficient  -1:  d=10^ell*(9+10*(Z-1)),   Z>=1.    (3.4)
```

The inequalities on `Z` follow directly from `d>0`; for example,
`-1+10Z>0` implies `Z>=1`. Thus there are unique

```text
rho(p) in {1,8,9},  A(p) in Nat
```

such that

```text
d(p) = 10^ell(p) * (rho(p)+10*A(p)).                        (3.5)
```

T16's machine-checked `tenValuation_lowDecimalCoefficient` now gives

```text
tenValuation(d(p)) = ell(p).                                (3.6)
```

For `0<=ell<N` and `rho in {1,2,8,9}`, define the exact finite subdomain

```text
P_B(ell,rho)
 = {p in primitiveRecordDomain 8 1 Q0 m N B:
      exists A in Nat,
        d(p)=10^ell*(rho+10*A)}.                            (3.7)
```

Equations (3.3)-(3.6) prove the disjoint partition

```text
primitiveRecordDomain 8 1 Q0 m N B
 = disjoint union over 0<=ell<N of
     (P_B(ell,1) union P_B(ell,8) union P_B(ell,9)),         (3.8)

P_B(ell,2) = empty.                                         (3.9)
```

Indeed, different `ell` are separated by (3.6), and at fixed `ell` different
residues are separated modulo ten after dividing by `10^ell`. This also proves
that T49's realized valuation parameter set is contained in `{0,...,N-1}`.
No record, orientation, or valuation fiber is omitted.

## 4. Complete inclusive-frequency valuation audit

Although no `h` occurs in (2.5), the frequency split motivating the proposed
exception can be audited exactly. T29's inclusive frequency domain is

```text
1 <= h <= 10^m.                                             (4.1)
```

T16 and T32 give the unique reduction

```text
h=10^e*u,  10 does not divide u,  e<=m,
e=m if and only if h=10^m.                                 (4.2)
```

Combining (3.5) and (4.2), ordinary prime valuations give

```text
tenValuation(h*d(p)) = e+ell+tau,
tau = min(v_2(u)+v_2(rho+10A),
          v_5(u)+v_5(rho+10A)).                             (4.3)
```

Here `v_p(n)` is the largest exponent of the prime `p` dividing the positive
integer `n`. Formula (4.3) is the identity
`tenValuation(n)=min(v_2(n),v_5(n))` together with ordinary prime-valuation
additivity on products.

This yields all cases:

```text
rho=1 or 9: tau=0;
rho=2:      the record stratum is empty;
rho=8 and 5 does not divide u: tau=0;
rho=8 and 5 divides u:
  tau=min(v_5(u),v_2(8+10A))>0.                             (4.4)
```

In the last line `10` not dividing `u` forces `u` odd. At the inclusive
endpoint `h=10^m`, one has `u=1`, so `tau=0` and

```text
tenValuation(10^m*d(p))=m+ell.                              (4.5)
```

Thus the cross-valuation calculation is correct and exhaustive. It cannot,
however, define the exceptional part of T49's predicate: `h` has already been
summed out before (2.5), and the shell condition there is on `d(p)*pi`, not on
`h*d(p)*pi`. A corrected partition of T49 must retain all three residue
sectors in (3.8).

## 5. One-block counterfamilies

Fix arbitrary

```text
Q0 in Nat,  0<s<1,  t in Nat,
L=2^t,      m=1,     N=4L+1.                               (5.1)
```

Since `N-1=2^(t+2)`, the definition of the canonical binary partition gives
exactly one block

```text
B = [1,4L+1),  B.start=1,  B.level=t+2,  B.finish=N.        (5.2)
```

Explicitly, `(N-1).bitIndices=[t+2]`, its reverse is unchanged, and
`dyadicPartitionFrom 0 [t+2]=[<1,t+2>]`; this is the complete list, not merely
a block containing the selected endpoints.

Its literal weight is

```text
w(B)=sqrt((4L+1)^2-1)=sqrt(N^2-1)<N.                       (5.3)
```

Partition its integer endpoints into four intervals, each of cardinality
`L`:

```text
I1=[1,L],          I2=[L+1,2L],
I3=[2L+1,3L],     I4=[3L+1,4L].                            (5.4)
```

At `(mu,c,m)=(8,1,1)`, T12's machine-checked theorem
`not_arithmeticExcluded_eight_one_at_one` says every positive lag survives,
independently of `Q0`. Its coordinate theorem says that every ordered pair of
distinct coordinates below `N` is an exact record. For `a>b`, write that
record explicitly as

```text
q(a,b) = (true,(a-b,b)).                                    (5.5)
```

Then

```text
orderedFirst(q(a,b))=a,
orderedSecond(q(a,b))=b,
signedDecimalFrequency(q(a,b))=10^a-10^b.                  (5.6)
```

### 5.1 Residue 1

Choose independently

```text
a1 in I1,  a2 in I2,  a3 in I3,  a0 in I4,                (5.7)
```

and set

```text
q+ = q(a0,a2),    q- = q(a3,a1),    p=(q+,q-).             (5.8)
```

Both lags are at least `L+1>=1`; both frequency endpoints lie in the exact
half-open block (5.2); and arithmetic exclusion is impossible by the cited
T12 theorem. The four exponent intervals are disjoint, so noncancellation is
automatic. Moreover `a0>=a3+1` and `a3>=a2`, whence

```text
10^a0 >= 10*10^a3 > 10^a3+10^a2,
```

and therefore

```text
d(p)=10^a0+10^a1-10^a2-10^a3>0.                           (5.9)
```

This proves the strict orientation in (2.2). The unique lowest exponent is
`a1`, carrying positive sign, so

```text
ell(p)=a1,       rho(p)=1.                                  (5.10)
```

The map from the four choices in (5.7) to `p` is injective, because (5.6)
recovers `(a0,a2)` from `q+` and `(a3,a1)` from `q-`. Hence this gives exactly
`L^4` distinct members in the parametrized subfamily of the residue-`1`
primitive domain; the full residue sector may contain more.

### 5.2 Residue 9

Choose independently

```text
a2 in I1,  a1 in I2,  a3 in I3,  a0 in I4,                (5.11)
```

and use the same definitions (5.8). The domain, lag, noncancellation,
positivity, and injectivity arguments are unchanged. Now the unique lowest
exponent is `a2`, carrying negative sign, so

```text
ell(p)=a2,       rho(p)=9.                                  (5.12)
```

This gives exactly `L^4` distinct records in the parametrized residue-`9`
subfamily; the full residue sector may contain more.

## 6. Exact shell and target comparison

At `m=1`, equations (2.7)-(2.8) give `K=3`, since
`2^3<10<=2^4`. The shells and their literal weights are

```text
[0,1/10]       weight 1,
(1/10,1/5]    weight 1/2,
(1/5,2/5]     weight 1/4,
(2/5,1/2]     weight 1/8.                                  (6.1)
```

T34's nearest-integer bound puts every real number in their union. Therefore

```text
W_1(x)>=1/8                                                     (6.2)
```

for every real `x`, including all `d(p)*pi`; no equidistribution,
irrationality measure, or unproved fixed-`pi` estimate is used.

Let `I_rho(Q0;1,N)` denote (2.5) restricted by the exact partition (3.7) to
residue `rho`. From the `L^4` records in either Section 5.1 or 5.2, (5.3) and
(6.2) give, separately for `rho=1` and `rho=9`,

```text
I_rho(Q0;1,4L+1)
 >= L^4/(8*w(B))
>  L^4/(8N).                                               (6.3)
```

All widths are positive and all shell weights are nonnegative. The disjoint
finite partition (3.8) therefore gives the exact decomposition

```text
I_prim(Q0;m,N)=I_1(Q0;m,N)+I_8(Q0;m,N)+I_9(Q0;m,N),         (6.3a)
```

and in particular `I_prim>=I_rho` for each retained residue.

For every `0<s<1`, since `N>=5`,

```text
N+N^2*10^(-s) < 2N^2.                                      (6.4)
```

Also `N=4L+1<=5L`. Dividing (6.3) by (6.4) yields the completely explicit
constant comparison

```text
I_rho(Q0;1,N) / (N+N^2*10^(-s))
 > L^4/(16N^3)
 >= L/2000,                 rho in {1,9}.                   (6.5)
```

Given any proposed `C>=0`, choose a power of two `L=2^t>2000C`. Then (6.5)
contradicts (2.9) at the positive parameters `m=1`, `N=4L+1`. This construction
works for every fixed `Q0` and every `0<s<1`. Consequently

```text
for every Q0 in Nat, every 0<s<1, and every real C>=0,
  not PrimitiveIncidenceAt 8 1 Q0 s C
```

for every `C>=0`, and hence

```text
not PrimitiveIncidence 8 1 Q0                              (6.6)
```

for every natural `Q0`.

## 7. Corrected partition and claim boundary

The arithmetic partition is exactly

```text
residue 1: lowest signed coefficient +1;
residue 8: lowest signed coefficient -2;
residue 9: lowest signed coefficient -1;
residue 2: empty because coefficient +2 contradicts d>0.   (7.1)
```

What must be corrected is the analytic model. Residues `1` and `9` are not
generic target-scale strata: each has the infinite counterfamily (5.1)-(5.12)
and the lower bound (6.3). Residue `8` is therefore not the unique exceptional
sector. Its frequency cross-valuation subclass (4.4) is not present in T49's
incidence after the frequency sum has been replaced by shells. The corrected
T49-level partition is simply the three shell incidences obtained from
(3.8), with two of them already refuting the proposed all-scale estimate.

This counterfamily refutes T49's sufficient primitive incidence hypothesis,
not the signed primitive contribution itself: T49 took absolute values and
then used a positive shell majorant, so cancellation among the `L^4` signed
kernel terms is intentionally absent from (2.5). It also does not refute
T29's width-weighted square-function predicate, C2, C1, or the canonical
collision estimate. Any replacement primitive frontier must preserve signed
aggregation or introduce additional decay across valuation fibers; merely
isolating residue `8` cannot repair T49's predicate.

## 8. Verification checklist

1. Source: canonical byte hash is displayed and the problem is labeled as a
   sibling A12 attack.
2. Domain: (2.2)-(2.4) retain both records, strict positive orientation,
   arithmetic survival, noncancellation, and all four exponent coordinates.
3. Partition: (3.1)-(3.9) prove exhaustiveness, disjointness, valuation, the
   three realized residues, and the empty residue `2`.
4. Frequencies: (4.1)-(4.5) retain `1<=h<=10^m`, the endpoint `h=10^m`, and
   every zero or positive product cross-valuation case.
5. Blocks and weights: (5.2)-(5.3) use the exact half-open canonical block and
   literal square-root width.
6. Records: (5.7)-(5.12) give `L^4` injectively parametrized exact records in
   each counterfamily for every `t,Q0` in the stated ranges.
7. Shells: (2.6)-(2.8) and (6.1) retain all open/closed endpoints, terminal
   cap, terminal depth, and weights.
8. Constants: the lower shell constant is `1/8`; the comparison constants are
   `8`, `16`, `5^3=125`, and `2000=16*125`; no asymptotic notation is used in
   the contradiction.
9. Parameters: `Q0,t` are arbitrary naturals, `L=2^t`, `m=1`, `N=4L+1`,
   `0<s<1`, and the failed T49 constant is any real `C>=0`.
10. Claim boundary: no signed-sector, T29, C2, C1, or canonical collision
    conclusion is asserted.
