# T85: Uniform bound for the grouped T61 square

Status: `proof sketch` with a complete elementary proof and exact finite
replay.  The T56, T58, and T61 interfaces cited below are `machine-checked`.
No claim from the T83 or T84 notes is a premise.  This note proves no
fixed-`pi` estimate and no instance of C7, C2, or C1.

## 1. Provenance and normalized task

The canonical problem is locally formulated and has no original external
source URL.  Its byte-exact delivered copy is
`pi-positive-decimal-factor-entropy.txt`, SHA-256

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6.
```

It asks whether one fixed `eta>0` gives
`p_pi(n)>=10^(eta*n)` for every sufficiently large `n`.  T85 neither changes
nor resolves that question.  The task here is only the deterministic grouped
coefficient square attached to T61's signed short-sector residual.

The T85-specific conventions and ambiguous quantifiers are fixed as follows.

1. The parameters `mu,c` are arbitrary reals and `Q0` is an arbitrary natural
   number.  The bound below is uniform in all three; no effective
   irrationality hypothesis is assumed.
2. Scale indices are natural numbers.  T61's nonempty analytic range starts at
   `n=1`; define `B_0(q)=0`.  Thus `n<=N` literally includes `n=0` without
   changing any sum.
3. Frequencies `q` are positive integers.  At each finite `N`, the notation
   `sum_q` means the sum over the finite union of the supports at `0<=n<=N`.
   Equivalently, extend every `B_n` by zero to all positive integers.
4. `|x|^2=x^2` for the real grouped coefficients.  The T61 zero Fourier mode
   is not included in `B_n` or `D_N`.
5. Every division in `n/2` and `10^n/2` is natural-number division before
   coercion.  All other divisions displayed below are real divisions.

## 2. Machine-checked boundary

The exact imported sources and declarations are:

| Item | Declaration | Exact role | SHA-256 |
|---|---|---|---|
| T25 | `structuredDenominator`, `ArithmeticExcluded` | exact structured denominator and arithmetic mask | `86639d8f8adbb5cf54a474fe89760cbeecd243e9f0bcb3768a16a23dab3ee88c` |
| T56 | `t56SampleLength`, `mem_sparse_short_sector_iff` | `L_n=10^(n/2)` and the strict short-lag range | `41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc` |
| T58 | `bandwidth`, `mem_positiveFejerFrequencies_iff`, `phi`, `phi_collision_after_ten_reduction` | `H_n=10^n/2`, strict positive multipliers, and the integer frequency | `04b3808f208db000284cf369467f4d2ffb907b1af44b30fcada8451b8503016d` |
| T61 | `mem_residualShortRectangle_iff`, `vaalerCoefficient_explicit`, `signedStructuredDenominatorSum`, `structuredVaalerMajorantTotal_eq_completeExpression` | exact residual mask, signed coefficient, and complete finite expansion | `61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993` |

The arithmetic mask is the `machine-checked` T25 definition imported by T61:

```text
ArithmeticExcluded(mu,c,Q0,n,j,r) iff
  Q0 <= 10^j*(10^r-1) and
  10^(-n) <= 10^j*(10^r-1)
    * (c/(10^j*(10^r-1))^mu).                         (2.1)
```

Equality at the decimal cutoff is included in the mask.  Nothing in the proof
below uses a sign, size, or monotonicity property of this predicate; deleting
labels can only decrease the cardinalities used in the estimates.

## 3. Exact coefficients and finite grouping

For `n>=1`, put

```text
L_n=10^(floor(n/2)),       H_n=10^n/2,
R_r=10^r-1,                Phi(h,r,j)=h*10^j*R_r.       (3.1)
```

Since `10^n` is even, `H_n=10^n/2` also as a real identity.  Define the exact
masked T61 label and tuple sets

```text
R_n(mu,c,Q0)={(r,j):
  0<r<n, r<L_n, 0<=j<L_n-r,
  not ArithmeticExcluded(mu,c,Q0,n,j,r)},              (3.2)

Omega_n(mu,c,Q0)={(h,r,j):
  1<=h<H_n and (r,j) in R_n(mu,c,Q0)}.                  (3.3)
```

The explicit `r<L_n` in (3.2) is redundant once `j<L_n-r` is satisfiable,
but is retained because T56's `shortResidualLags` contains that strict
endpoint.  Thus (3.2) is exactly T61's nested
`shortResidualLags`/`residualStartDomain`, not a rectangular enlargement.

For `1<=h<H_n`, T61's literal signed coefficient is

```text
a_n(h)=H_n^(-1)*[
  sin(pi*h/H_n)/pi
  +2*(1-h/H_n)*cos(pi*h/H_n)].                          (3.4)
```

No absolute value or Fejer weight is substituted into (3.4).  For every
positive integer `q`, define

```text
B_n(q)=(2/L_n)*
  sum_{(h,r,j) in Omega_n, Phi(h,r,j)=q} a_n(h),         (3.5)
B_0(q)=0,
Q_n={Phi(h,r,j):(h,r,j) in Omega_n},
Q_<=N=union_{1<=n<=N} Q_n,
D_N=sum_{q in Q_<=N} |sum_{0<=n<=N} B_n(q)|^2.          (3.6)
```

All sums in (3.5)-(3.6) are finite.  If `S_n(x)` denotes T61's
`signedStructuredDenominatorSum`, finite regrouping by the integer map `Phi`
gives exactly

```text
S_n(x)/L_n=sum_{q in Q_n} B_n(q)*cos(2*pi*q*x).          (3.7)
```

Indeed, T61 has the outer factor `2`, then one copy of `a_n(h)` for every
tuple.  This is the source of `2/L_n` in (3.5).  Its zero mode is separately
`2*residualStructuredCard/H_n`; it is absent from (3.5)-(3.7).

## 4. Complete duplicate identity

For a positive `h`, write uniquely

```text
h=10^v(h)*u(h),       10 does not divide u(h).           (4.1)
```

Because `gcd(10,10^r-1)=1`, two tuples have the same positive frequency if
and only if

```text
v(h1)+j1=v(h2)+j2,
u(h1)*(10^r1-1)=u(h2)*(10^r2-1).                       (4.2)
```

For completeness, let `g=gcd(r1,r2)`, `G=10^g-1`,

```text
U=(10^r1-1)/G,       V=(10^r2-1)/G.                    (4.3)
```

Here is a derivation rather than an appeal to the T83/T84 notes.  If `b=qa+s`
with `0<=s<a`, reduction modulo `10^a-1` gives

```text
10^b-1 congruent to 10^s-1 (mod 10^a-1).
```

Euclid's algorithm on the exponents therefore gives
`gcd(10^a-1,10^b-1)=10^gcd(a,b)-1`; the terminal case is
`gcd(10^a-1,0)=10^a-1`.  Applying this with `a=r1,b=r2` gives
`gcd(U,V)=1`.  After cancelling `G`, the second equality in (4.2) is
`u(h1)U=u(h2)V`.  Coprimality implies `V` divides `u(h1)` and `U` divides
`u(h2)`, so there is a unique positive integer `t` such that

```text
u(h1)=V*t,           u(h2)=U*t.                         (4.4)
```

Conversely (4.4) gives the equality immediately.  Since `U,V` and both
primitive parts are coprime to ten, `t` is not divisible by ten.

Equations (4.2)-(4.4), together with two independent copies of (3.2)-(3.3),
are the complete duplicate classification.  The two scale indices may be
equal or unequal: they affect tuple legality and `a_n(h)`, but not the integer
frequency equality.  This identity is replayed at finite scales, but the
universal bound below needs only the sharper elementary fiber count in Step 2.

## 5. Uniform one-scale square estimate

Fix arbitrary `mu,c,Q0`.  For `n>=1`, define

```text
E_n=sum_{q in Q_n}|B_n(q)|^2.                           (5.1)
```

We prove, without using T83 or T84,

```text
E_n < 36*n^3/(H_n*L_n) for n>=2,       E_1=0.           (5.2)
```

### Step 1: coefficient envelope and tuple count

For `1<=h<H_n`, let `y=h/H_n`, so `0<y<1`.  Using `pi>1`,
`|sin|<=1`, and `|cos|<=1` in the literal formula (3.4),

```text
|a_n(h)|
 <=H_n^(-1)*[1/pi+2*(1-y)]
 <3/H_n.                                                (5.3)
```

There are at most `n-1` legal lags.  For each lag there are at most `L_n`
starts, and there are exactly `H_n-1` positive multipliers.  The mask can only
delete tuples.  Hence

```text
|Omega_n| <=(H_n-1)*(n-1)*L_n.                          (5.4)
```

### Step 2: every one-scale frequency fiber has at most `n(n-1)` tuples

Fix a positive frequency `q` and one lag `r`.  Suppose its representations at
that lag have distinct starts

```text
j_1<j_2<...<j_k.
```

Writing the corresponding multipliers as `h_i`, equality of frequencies gives

```text
h_1=10^(j_k-j_1)*h_k >=10^(k-1).                        (5.5)
```

Here `j_k-j_1>=k-1` and `h_k>=1`.  But `h_1<H_n<10^n`, so strict monotonicity
of powers of ten gives `k-1<n`, hence `k<=n`.  There are at most `n-1` legal
lags.  Therefore every complete masked fiber satisfies

```text
|{(h,r,j) in Omega_n:Phi(h,r,j)=q}| <=n*(n-1).          (5.6)
```

This argument permits all unequal-lag and decimal-valuation duplicates; none
are omitted.  Again, the mask only removes representations.

### Step 3: Cauchy-Schwarz within each exact fiber

Apply Cauchy-Schwarz separately to every fiber in (3.5), then (5.3)-(5.6):

```text
E_n
 =(4/L_n^2)*sum_q |sum_{alpha in fiber(q)}a_n(h_alpha)|^2
 <=(4/L_n^2)*n*(n-1)*sum_{alpha in Omega_n}|a_n(h_alpha)|^2
 <(4/L_n^2)*n*(n-1)*(H_n-1)*(n-1)*L_n*9/H_n^2
 =36*n*(n-1)^2*(H_n-1)/(L_n*H_n^2)
 <36*n^3/(H_n*L_n).                                    (5.7)
```

At `n=1` there is no positive `r<n`, so `Omega_1`, `Q_1`, and `E_1` are empty.
This proves (5.2) at every scale and for every arithmetic mask.

## 6. All-scale bound for `D_N`

For a fixed `N`, regard each `B_n` as a vector indexed by the finite set
`Q_<=N`, extending it by zero off `Q_n`.  The finite-dimensional triangle
inequality in Euclidean norm gives

```text
sqrt(D_N)=||sum_{n=1}^N B_n||_2
 <=sum_{n=1}^N ||B_n||_2
 =sum_{n=2}^N sqrt(E_n).                                (6.1)
```

Since `H_n*L_n=(10^n/2)*10^floor(n/2)`, (5.2) gives

```text
sqrt(E_n)
 <6*sqrt(2)*n^(3/2)*10^(-(n+floor(n/2))/2).             (6.2)
```

For every `n>=1`,

```text
floor(n/2)>=(n-1)/2,       sqrt(2)<2,
10^(1/4)<2,                 10^(-3/4)<1/5,
n^(3/2)<=n^2.                                           (6.3)
```

The two decimal inequalities follow after raising positive quantities to the
fourth power: `10<16` and `5^4=625<1000=10^3`.  Combining (6.2)-(6.3),

```text
sqrt(E_n)<24*n^2/5^n.                                   (6.4)
```

The differentiated geometric-series identity gives

```text
sum_{n=0}^infinity n^2*x^n=x*(1+x)/(1-x)^3, |x|<1.
```

At `x=1/5`, subtracting the `n=1` term yields

```text
sum_{n=2}^infinity n^2/5^n=15/32-1/5=43/160.           (6.5)
```

Therefore, for every `N>=1`,

```text
sqrt(D_N)<24*(43/160)=129/20,
D_N<(129/20)^2=16641/400<42.                            (6.6)
```

For `N=0`, (3.6) is an empty sum and `D_0=0`.  We have proved the requested
explicit all-scale linear statement, uniformly in the T61 mask parameters:

```text
For every mu,c in R, Q0,N in N,
  D_N <=42*N.                                           (T85)
```

Indeed the `N=0` case is equality, while for `N>=1`, (6.6) gives
`D_N<42<=42*N`.  The stronger uniform bound `D_N<42` holds for every `N>=1`.

## 7. Relation to the T84 roadmap and exact scope

The T84 note argues, at sketch verification level, that a selected family has
nonsummable grouped `l1` mass.  No part of that argument is used here.  The
direct square estimate (5.7) explains why such an `l1` phenomenon need not
survive at the signed square scale: the `2/L_n` and `1/H_n` factors make the
one-scale `l2` norms summable even after allowing every exact duplicate.

This deterministic result does not evaluate
`cos(2*pi*q*Real.pi)`, does not bound T61's signed polynomial at `Real.pi`, and
does not control distinct-frequency fixed-`pi` covariance.  It proves no
short-incidence estimate, no fixed-`pi` statement, and no C7, C2, or C1
conclusion.

## 8. Replay

From a directory containing only the delivered artifacts, run

```sh
sh ./verify.sh
```

The dependency-free checker uses exact integers and rational numbers.  It
checks the canonical hash; literal T61 ranges for two exact `mu=2,c=1` masks;
direct, ten-reduced, and repunit-gcd collision partitions; symbolic
`2/L_n` grouping; the ordered-pair expansion of `D_N`; one-scale tuple and
fiber bounds; and every rational constant in (6.3)-(6.6).  The finite cases are
an `experiment`, not evidence for the universal quantifiers.  Steps 1-6 are
the independently inspectable proof of those quantifiers.
