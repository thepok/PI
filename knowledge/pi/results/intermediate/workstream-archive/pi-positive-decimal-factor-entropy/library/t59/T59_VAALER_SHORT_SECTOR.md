# T59: a periodic Vaaler majorant for the strict sparse short sector

Status: `proof sketch`.  The finite T56/T58 interfaces cited below are
`machine-checked`; the specialized analytic argument is given in this note.
Final verdict: **NO KERNEL-ONLY WEAKENING (ABSTRACTLY INCOMPARABLE)**.  The
Vaaler premise and the T58 note's Fejer premise both imply T56's
short-incidence predicate.  Neither kernel dominates the other on the finite
arbitrary-phase model, so the Vaaler premise is not a weakening derivable from
the displayed finite interfaces.  Explicit abstract arrays separate every
unsupported interface direction.  No fixed-pi estimate, C7, C2, or C1 is
asserted.

## 1. Source, task, and ambiguities

The canonical question is locally formulated and has no original source URL.
The byte-exact statement is delivered as
`pi-positive-decimal-factor-entropy.txt`; its SHA-256 is

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

It asks whether one fixed `eta>0` gives
`p_pi(n)>=10^(eta*n)` for every sufficiently large `n`.  T59 does not answer
that question.  It compares two conditional analytic targets for T56's strict
short sector.

The only external analytic input is Theorem 18 (especially (7.14)) and the
bounded-variation specialization in Theorem 19, (7.24)--(7.27), of:

> J. D. Vaaler, "Some extremal functions in Fourier analysis," *Bulletin of
> the American Mathematical Society* 12 (1985), 183--216,
> <https://doi.org/10.1090/S0273-0979-1985-15349-2>, pp. 210--212.

The retrieved source is delivered as `vaaler-1985.pdf`, SHA-256
`e606ccef342e72d7e48b59a7da7f8577f72fd351ce32989b23dd85e9e8cd4c1a`,
and as `vaaler-1985.txt`, SHA-256
`e1da636f3ae9b42b94aabd20fcb1ad99a5e194abc0aefdf536b28d85b501add4`.
The formulas below specialize Vaaler's degree `N` result with `N=H-1` and
derive every coefficient directly.

### Ambiguities fixed

1. `n` is natural, and every eventual assertion has `n>=N>=1`.
2. `L_n=10^(n/2)`, where `/` is natural-number division.
3. `H_n=10^n/2`, with natural division.  For `n>=1`, `2H_n=10^n`.
4. Lags and starts are exactly `0<r<n` and `0<=j<L_n-r`.  Both `r=n`
   and `j=L_n-r` are excluded.
5. Frequencies are exactly `1<=h<H_n`; zero is displayed separately and
   `h=H_n` is absent.
6. Every circular cutoff is strict: `rho(x)<10^(-n)=1/(2H_n)`.
7. The factor two in T56's count restores both orientations.  The analytic
   sums below run once over the upper-triangular `(r,j)` rectangle.
8. "Signed premise" means an upper bound for the complete real Fourier sum;
   individual Vaaler coefficients may be negative.
9. An abstract separating array preserves all finite ranges and masks but not
   the arithmetic relation `x=pi*10^j*(10^r-1)`.  Such an array proves
   non-derivability from the interfaces, not falsity for pi.

## 2. Kernel-checked finite interface

Fix `mu,c in R` and `Q0 in N`.  For `n>=1`, put

```text
L=L_n:=10^(n/2),             H=H_n:=10^n/2,
q_(j,r):=10^j*(10^r-1),      x_(j,r):=pi*q_(j,r) mod 1.       (2.1)
```

T56's imported arithmetic mask is

```text
E_n(r,j) iff
  Q0 <= q_(j,r)
  and 10^(-n) <= q_(j,r) * (c/q_(j,r)^mu),

epsilon_n(r,j):=1_(not E_n(r,j)).                             (2.2)
```

Equality is included in the second condition because the near-return cutoff
is strict.  T58's checked rectangle theorem gives exactly

```text
R_n := {(r,j): 0<r<n and 0<=j<L-r}.                           (2.3)
```

Let

```text
X_n := {(r,j) in R_n: epsilon_n(r,j)=1},
A_n := |{(r,j) in X_n: rho(x_(j,r))<1/(2H)}|.                 (2.4)
```

Unfolding the finite definitions audited by T56 gives

```text
shortResidualPairCount(mu,c,Q0,n,L_n)=2*A_n.                 (2.5)
```

Thus T56's kernel-checked predicate is literally

```text
(I_pi): exists A>0, exists N>=1, for every n>=N,
        2*A_n <= A*L_n.                                      (2.6)
```

No instance of (2.6) is known.  Also

```text
|X_n| <= |R_n| <= nL_n.                                      (2.7)
```

For later abstract separations, if `n>=2` then `L_n>=n` and the full
rectangle has exact size

```text
M_n:=|R_n|=sum_(r=1)^(n-1)(L_n-r)
            =(n-1)L_n-n(n-1)/2 >= (n-1)L_n/2.                (2.8)
```

The inequalities `L_n>=n` and `H_n>=n` follow immediately by induction from
their decimal definitions (the cases `n=1,2` start the two inductions).

## 3. The explicit periodic majorant

Write `e(x):=exp(2*pi*i*x)` and use the midpoint sawtooth

```text
psi(x) = {x}-1/2 if x is not an integer,
         0       if x is an integer.                          (3.1)
```

For an integer `H>=2`, define, for `0<|t|<1`,

```text
W(t):=pi*t*(1-|t|)*cot(pi*t)+|t|,                             (3.2)

J_H(x):=-sum_(0<|h|<H) W(h/H)/(2*pi*i*h) e(hx),              (3.3)

K_(H-1)(x):=sum_(|h|<H)(1-|h|/H)e(hx)
           =1/H * (sin(pi*H*x)/sin(pi*x))^2,                 (3.4)
```

where (3.4) has the continuous value `H` at integers.  Vaaler's periodic
sawtooth inequality in this normalization is

```text
|psi(x)-J_H(x)| <= K_(H-1)(x)/(2H) for every real x.          (3.5)
```

Put `delta=1/(2H)`.  The midpoint-valued circular interval is

```text
chi_H#(x):=1/H+psi(x-delta)-psi(x+delta)
 = 1     if rho(x)<delta,
   1/2   if rho(x)=delta,
   0     if rho(x)>delta.                                    (3.6)
```

Define the promised degree-`H-1` periodic Vaaler majorant by

```text
M_H(x):=1/H+J_H(x-delta)-J_H(x+delta)
        +[K_(H-1)(x-delta)+K_(H-1)(x+delta)]/(2H).            (3.7)
```

Apply (3.5) once to each sawtooth in (3.6).  This gives, at every real `x`,

```text
1_(rho(x)<1/(2H)) <= chi_H#(x) <= M_H(x).                    (3.8)
```

In particular `M_H(x)>=0`.  Strict endpoints are harmless but not erased:

```text
1_(rho(+-delta)<delta)=0,  chi_H#(+-delta)=1/2,
M_H(+-delta)=1.                                               (3.9)
```

The last equality follows from `J_H(0)=0`,
`J_H(1/H)=psi(1/H)=1/H-1/2`, `K_(H-1)(0)=H`, and
`K_(H-1)(1/H)=0`.  These are finite interpolation identities, not limiting
endpoint conventions.

## 4. Every Fourier coefficient

Write

```text
M_H(x)=sum_(h in Z) m_H(h)e(hx).                              (4.1)
```

The constant `1/H` in (3.7) and the two Fejer zero modes give

```text
m_H(0)=2/H.                                                   (4.2)
```

For `0<|h|<H`, shifting the two sawtooth terms gives

```text
W(h/H)*sin(pi*h/H)/(pi*h),                                   (4.3)
```

where evenness is understood when `h<0`.  The two shifted Fejer terms give

```text
(1/H)*(1-|h|/H)*cos(pi*h/H).                                 (4.4)
```

Therefore

```text
m_H(h)=W(h/H)*sin(pi*h/H)/(pi*h)
       +(1/H)*(1-|h|/H)*cos(pi*h/H),       0<|h|<H,           (4.5)
m_H(h)=0,                                  |h|>=H.            (4.6)
```

The coefficients are real and even.  For `1<=h<H`, expansion of (3.2)
simplifies (4.5) to

```text
c_H(h):=m_H(h)
 =1/H*[sin(pi*h/H)/pi
       +2*(1-h/H)*cos(pi*h/H)].                              (4.7)
```

Thus the complete real expansion is

```text
M_H(x)=2/H+2 Re sum_(h=1)^(H-1)c_H(h)e(hx).                  (4.8)
```

This is genuinely signed.  For example, writing `y=pi/H`,

```text
c_H(H-1)=[sin(y)-2y cos(y)]/(pi*H)<0                         (4.9)
```

for `H>=3`, since `tan(y)<2y` for `0<y<=pi/3`.  Hence neither an exact
absolute-value replacement nor an exact coefficientwise-positive replacement
preserves (4.8); ordinary triangle-inequality upper bounds remain valid but
discard the signed cancellation isolated here.

## 5. The resulting fixed-pi premise

Specialize (4.8) to `H=H_n` and define the signed sum

```text
P_n(pi):=
  2 Re sum_(h=1)^(H_n-1)c_(H_n)(h)
       sum_((r,j) in R_n) epsilon_n(r,j)
         e(h*pi*10^j*(10^r-1)).                              (5.1)
```

The exact finite identity is

```text
sum_((r,j) in X_n) M_(H_n)(x_(j,r))
  =2|X_n|/H_n+P_n(pi).                                       (5.2)
```

The Vaaler fixed-pi premise is

```text
(V_pi): exists B>0, exists N>=1, for every n>=N,
        P_n(pi) <= B*L_n.                                    (5.3)
```

This is an unproved estimate at the one fixed phase `pi`.  It is equivalent,
up to explicit constants, to requiring the nonnegative left side of (5.2) to
be `O(L_n)`: the latter bounds `P_n(pi)` because `2|X_n|/H_n>=0`, while
(2.7) and `H_n>=n` bound the zero mode by `2L_n`.

Summing (3.8), then using (2.7), gives

```text
A_n <= 2|X_n|/H_n+P_n(pi) <= (2+B)L_n.                       (5.4)
```

Consequently

```text
(V_pi) => (I_pi), with T56 constant A=4+2B
and the same cutoff N.                                       (5.5)
```

This implication proves no instance of either premise.

## 6. Reproved T58 Fejer implication

The T58 prose note's unproved Fejer premise, restated rather than treated as
an established result, is

```text
(F_pi): exists D>0, exists N>=1, for every n>=N,

  1/(H_n*L_n) *
  sum_((r,j) in R_n) epsilon_n(r,j)
    K_(H_n-1)(pi*10^j*(10^r-1)) <= D.                        (6.1)
```

If `0<rho(x)<1/(2H)`, choose that representative.  Concavity gives
`sin(pi*H*rho)>=2H*rho`, while `sin(pi*rho)<=pi*rho`.  If `rho(x)=0`,
the continuous value is instead `K_(H-1)(x)/H=1`.  Formula (3.4) therefore
gives in both cases the strict central bound

```text
K_(H-1)(x)/H >= 4/pi^2.                                      (6.2)
```

Nonnegativity of the Fejer kernel and (6.2) imply

```text
A_n <= pi^2/(4H_n)
       *sum_((r,j) in X_n)K_(H_n-1)(x_(j,r)).                 (6.3)
```

Hence

```text
(F_pi) => (I_pi), with T56 constant A=pi^2*D/2
and the same cutoff N.                                       (6.4)
```

Again, (6.4) is only a conditional implication.

## 7. Every reverse and cross direction

The positive implications established for the actual fixed-pi predicates are

```text
(V_pi) --> (I_pi) <-- (F_pi).                                (7.1)
```

The following exact abstract arrays show that none of the other four arrows
holds in the universal arbitrary-phase model determined by the finite ranges,
masks, strict cutoff, and displayed kernels.  They do not decide whether extra
arithmetic properties of the one fixed-pi phase could imply another arrow.
For each `n>=2`, use every label in `R_n`, set every mask to one, and assign
the same displayed abstract phase to all `M_n` labels.  By (2.8),
`M_n/L_n >= (n-1)/2`, so a fixed positive contribution per label is not
`O(L_n)`.

### 7.1 Incidence does not imply either analytic premise

Assign the strict endpoint

```text
x=delta_n=1/(2H_n).                                         (7.2)
```

The strict incidence count is zero.  But (3.9) gives `M_H(x)=1`, so the
signed contribution in (5.2) is `1-2/H`, at least `3/5` because `H_n>=5`.
Also

```text
K_(H-1)(delta)/H
 =1/[H^2*sin^2(pi/(2H))] >=4/pi^2.                           (7.3)
```

Thus the zero incidence count satisfies the incidence predicate with any
chosen positive constant but violates both uniform analytic bounds.  This
simultaneously separates, in the arbitrary-phase model,

```text
(I) -/-> (V),       (I) -/-> (F).                            (7.4)
```

The strict endpoint is essential: replacing `<` by `<=` would invalidate the
zero incidence assertion.

### 7.2 Fejer does not imply Vaaler

Assign

```text
x=1/H.                                                       (7.5)
```

The Fejer factor is exactly zero because `sin(pi*H*x)=0` but
`sin(pi*x)!=0`.  The Vaaler value is bounded away from zero.  Here is an
explicit check.  Put `a=pi/(2H)` and, for odd `m`, put

```text
A_m:=sum_(h=1)^(H-1)(1-h/H)cos(pi*m*h/H),
C_m:=sum_(h=1)^(H-1)sin(pi*m*h/H).
```

Differentiating the finite geometric series at
`z=exp(pi*i*m/H)`, where `z^H=-1`, gives

```text
A_m=-1/2+csc^2(m*a)/(2H),       C_m=cot(m*a).                 (7.6)
```

Using `cos(u)cos(2u)=[cos(u)+cos(3u)]/2` and
`sin(u)cos(2u)=[sin(3u)-sin(u)]/2` in (4.8) therefore gives

```text
M_H(1/H)
 =[csc^2(a)+csc^2(3a)]/H^2
   +[cot(3a)-cot(a)]/(pi*H).                                 (7.7)
```

For `H>=5`, `csc^2(t)` decreases on `[a,3a]`, so

```text
cot(a)-cot(3a)=integral_a^(3a)csc^2(t)dt
              <=2a*csc^2(a).
```

Using `H=pi/(2a)` and `sin(3a)<=3a` in (7.7) yields

```text
M_H(1/H)>=4/(9pi^2).                                         (7.8)
```

The signed contribution is `M_H(1/H)-2/H`.  For `H>=90` it is at least
`2/(9pi^2)>0`; all `n>=3` have `H_n>=500`.  Therefore the Fejer sum is zero
while the signed Vaaler sum is not `O(L_n)`, proving in the arbitrary-phase
model

```text
(F) -/-> (V).                                                 (7.9)
```

### 7.3 Vaaler does not imply Fejer

Assign

```text
x=3/(2H).                                                     (7.10)
```

The finite interpolation identity is

```text
M_H(3/(2H))=0.                                               (7.11)
```

For inspection, let
`A_m=sum_(h=1)^(H-1)(1-h/H)cos(pi*m*h/H)` and
`C_m=sum_(h=1)^(H-1)sin(pi*m*h/H)`.  Geometric summation gives
`A_2=A_4=-1/2` and `C_2=C_4=0`.  Substitution into (4.8) gives
`2/H+(2/H)(A_2+A_4)+(1/(pi*H))(C_4-C_2)=0`, proving (7.11).

Thus the signed sum per label is `-2/H`, so (V) holds trivially.  In contrast,

```text
K_(H-1)(3/(2H))/H
 =1/[H^2*sin^2(3pi/(2H))] >=4/(9pi^2).                       (7.12)
```

The Fejer sum is not `O(L_n)`, proving in the arbitrary-phase model

```text
(V) -/-> (F).                                                 (7.13)
```

All phases in Sections 7.2--7.3 lie strictly outside the near-return interval.

## 8. Verdict and scope

**NO KERNEL-ONLY WEAKENING (ABSTRACTLY INCOMPARABLE).**  The signed Vaaler
target (5.3) is a valid alternative sufficient premise for T56's
short-incidence predicate, with the explicit constant in (5.5).  It is not a
weakening that follows from the T58 Fejer premise by the audited finite kernel
interfaces: the exact zeros (7.5) and (7.10) separate the two kernels in
opposite directions in the universal arbitrary-phase model.  T56's strict
count likewise does not control either analytic tail in that model.

For the actual coupled phases `pi*10^j*(10^r-1)`, only the two arrows in
(7.1) are asserted.  The abstract arrays do not prove that any reverse arrow
is false specifically for pi.  They prove that such an arrow cannot be
obtained from T56/T58's finite combinatorial interfaces alone.  Any actual
cross implication would require new fixed-phase arithmetic information, so
discarding Fejer tails does not remove the fixed-phase obstruction.

In particular this note asserts none of `(V_pi)`, `(F_pi)`, `(I_pi)`, C7, C2,
or C1, and makes no unconditional claim about decimal factors of pi.

## 9. Replay

The proof sketch consists of the displayed finite identities and inequalities
above.  The accompanying script is only an `experiment` checking formulas at
finite scales:

```sh
python3 t59_replay.py --write replay.json
cmp replay.json replay_expected.json
```

From a directory containing only the delivered artifacts, `sh ./verify.sh`
checks all pinned hashes and the replay.

## 10. Kernel-checked declarations used

No new Lean theorem is claimed.  The finite interfaces used are:

```text
DecimalFactorComplexity.T56LagSectorAudit.mem_sparse_short_sector_iff
DecimalFactorComplexity.T56LagSectorAudit.sparseShortRepunitIncidenceBound_iff_quantifiers
DecimalFactorComplexity.T58TriangularFejerAudit.mem_positiveFejerFrequencies_iff
DecimalFactorComplexity.T58TriangularFejerAudit.mem_shortRectangle_iff
```

The T56/T58 prose notes are unverified and are not premises.  Section 6
restates and rederives the T58 note's proposed Fejer implication.
