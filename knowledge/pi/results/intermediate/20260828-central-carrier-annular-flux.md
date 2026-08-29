# Central carrier and annular flux

Date: 2026-08-28 UTC

Claim label: universal identities and inequalities are `proof sketch`
(independently audited); the fixed hard-node values are an `experiment`.
This isolates a new positive central-carrier mechanism, but does not prove an
unbounded actual-π shell or endpoint estimate.

## Exact literal refinement carrier

For the T128 boundary kernel define

```text
Phi_m(y)=kappa_m(y/m).
```

Direct factorization gives

```text
Phi_m(y)=Lambda(y)*R_m(y),

Lambda(y)=(pi^2/2)*(1-4*y^2)*(sin(pi*y)/(pi*y))^4,

R_m(y)=sinc(pi*(1+2*y)/(2*m))*sinc(pi*(1-2*y)/(2*m))
       /sinc(pi*y/m)^4.
```

The power series for `log sinc` proves, for every integer `b>=1`, `m>=2`,
and `|y|<=1/2`,

```text
0 <= Phi_m(y) <= Phi_(b*m)(y) <= Lambda(y).
```

The inequalities are strict for `b>1` and `|y|<1/2`.  If an actual-π suffix
lies in the interior of the parent cylinder and
`y=q*(x_(n+1)-c_(q,A))`, its literal predecessor child keeps exactly this
normalized radius and receives `Phi_(10q)(y)>=Phi_q(y)>0`; every sibling is
nonpositive.  Interior membership is essential at the abstract level; π's
irrationality excludes rational cylinder endpoints.

## The carrier pays its local siblings

For the ten child kernels `K_d(a,s)` and

```text
b_q=1-cos(pi/(10*q)),
a_q=1-cos(pi/q),
delta_q=100*b_q-a_q,
```

root-of-unity summation gives exactly

```text
sum_(d<10) K_d(a,s)-kappa_q(s)
 = sin(pi*q*s)^4/(q^2*sin(pi*s)^4)
   *(delta_q-66*b_q*sin(pi*s)^2).
```

Elementary directed cosine bounds show that, for `q>=1000` and `|y|<=0.35`,

```text
0 <= -sum_(d != a) K_d(a,y/q)
     <= Phi_(10q)(y)-Phi_q(y).
```

Thus the refinement gain of one sufficiently central literal occurrence pays
the complete negative mass sent to all nine siblings.  The analogous
ten-point DFT estimate retains all five real character blocks: after
dephasing by the named predecessor digit, every sector lies within the same
refinement-gain radius of the literal one-hot carrier.

This monotonicity cannot be extended through the sign boundary.  It reverses
immediately outside `|y|=1/2`.  The useful universal exterior estimate is

```text
0 <= -Phi_m(y)
  <= pi^2*(4*y^2-1)*sin(pi*y)^4/(32*y^4)
  <= pi^2/(8*y^2),       1/2<|y|<=m/2.
```

Consequently, if `B_n=floor(m*x_n)` and `rho_m(B_n,C)` is circular label
distance, the total negative lobe at target `C` is bounded by the weighted
near-miss count

```text
N_(m,C)(W)
 <= (pi^2/8)*sum_(j>=1)
      #{n in W: rho_m(B_n,C)=j}/(j-1/2)^2.
```

Generic occupancy does not sign or sufficiently sharpen this target-specific
quantity.

## Primitive-endpoint decimation and decimal carry routing

An independent audit of the natural step `q -> 10q` gives two further exact
reductions (`proof sketch`).  Write `E_(q,A)(N)` for T139's
`primitiveBoundaryEndpoint`, `c=(2*A+1)/(2*q)`, and `a_q(g)` for its positive
boundary coefficient.  With

```text
delta_q(g)=10*a_(10q)(10*g)-a_q(g),
M_q=sum_(1<=g<2q) delta_q(g),
```

T172 gives `delta_q(g)>0` and `M_q<21/(10*q^2)` for `q>=1000`.  Only
frequencies `h=10*g` contribute to the child endpoint, so
`E_(10q,A+dq)(N)` is exactly independent of `d`.  Moreover,

```text
10*Re E_(10q,A+dq)(N)-Re E_(q,A)(N)
 = (kappa_q(x_N-c)-kappa_q(x_0-c))/2 + epsilon_(q,A)(N).
```

If `V(q)=max_(1<=g<2q) nu_10(g)`, then

```text
|epsilon_(q,A)(N)| <= 2*(V(q)+1)*M_q.
```

For `q=10^k`, `V(q)=k`, hence the error is strictly less than
`21*(k+1)/(5*q^2)`.  Iteration along any finite nested target chain has the
exact geometric weights `10^(j-k)`; its total defect from a base
`q_0=10^k` is bounded by

```text
21/(5*q_0^2) *
  ((log_10(q_0)+1)/(1-10^-2) + 10^-2/(1-10^-2)^2).
```

Thus primitive endpoints reduce to a few literal target-kernel samples plus
a summable defect.  They remain a common scalar channel and cannot rank the
ten children.

The exterior loss has a complementary exact router.  Put

```text
B_q(n)=floor(q*x_n),              a_n=floor(10*x_n),
B_(10q)(n)=q*a_n+B_q(n+1).
```

For a parent target `A`, let `r_(q,A)(n)` be the representative of
`B_q(n+1)-A mod q` in `(-q/2,q/2]`, and set

```text
sigma_(q,A)(n)=(B_q(n+1)-A-r_(q,A)(n))/q in {-1,0,1},
d_(q,A)(n)=a_n+sigma_(q,A)(n) mod 10.
```

The routed child has circular label distance `|r_(q,A)(n)|`; every other
child has distance at least `q-|r_(q,A)(n)|>=q/2`.  Consequently, for any
time window `W`, each child's non-routed exterior remainder is at most

```text
|W|*tau_q,        tau_q=pi^2/(2*(q-1)^2),
```

and the sum over all ten children is at most `9*|W|*tau_q`.  The unresolved
routed vector is encoded exactly by the five real character blocks paired as
`r` with `10-r` (and the real `r=5` block):

A continuous-coordinate version sharpens the aggregate nine-sibling bound.
Put `y=q*x_(n+1)-A-1/2`, choose the unique half-open representative
`r=y-q*c in [-q/2,q/2)`, and route to `d=a_n+c mod 10`.  The other coordinates
have representatives `r+q*j` with absolute multiplicities
`1,1,2,2,3,3,4,4,5`; at the antipode use `r-5*q` when `r>0` and `r+5*q`
otherwise.  Therefore, per nonnegative unit occurrence weight,

```text
sum_(non-routed children) (-Phi_(10q)(Y_d))_+
 <= 233713*pi^2/(198450*q^2)
 < 11.631/q^2.
```

For signed weights, replace the weight by its absolute value.  Geometric
uniqueness at `|r|=q/2` is only the half-open tie convention; actual π avoids
the rational tie.  This improves only the already summable sibling error and
does not shrink the principal routed term.

```text
sum_(n in W, r_(q,A)(n)!=0)
  ell_n * e(r*(a_n+sigma_(q,A)(n))/10),       1<=r<=5.
```

Here `ell_n` is the literal routed negative-kernel weight.  Representation in
all five blocks does not imply that any block is nonzero or correctly signed.
The strongest robust direct certificate retains the normalized identities

```text
D_d/q=U_d-alpha,       F_d/q=V_d-beta,
J0/q^2=J(U,V;alpha,beta),
```

where `alpha,beta` are the two common endpoint thresholds and `U,V` retain
positive mass and the routed old/fresh shell vectors.  This handles changing
sign sets exactly, but is still a sufficient reformulation rather than a
source of sign.  The first fatal line is now precise: no theorem signs the
joint old/fresh carry--predecessor characters together with the ancestor
kernel samples for the actual π path.  Replacement failure need not reside
only in those characters; positive-mass alignment and the common thresholds
can also change the margins.

## Exact block carrier recurrence and principal routed obstruction

Endpoint decimation cancels the remaining orbit-window shift exactly.  Define
the signed block surplus

```text
S_(q,A)(M,L)
 = q*Re(primitiveBoundaryFourierBlockSum(q,A,M,L))-7*L/(3*q).
```

For `Q=10*q`, `C=A+d*q`, `mu_q=10*alpha_Q-alpha_q`, and `q=10^k>=1000`,
the independently audited block recurrence is

```text
(S_(Q,C)(M,L)-S_(q,A)(M,L))/q
 = (1/2)*sum_(M<=n<M+L)
       (10*kappa_Q(x_n-c_(Q,C))-kappa_q(x_(n+1)-c_(q,A)))
   -(L/2)*mu_q + 21*L/(10*q^2) - epsilon_(q,A)(M,L),
```

where `epsilon` is independent of the child `d` and

```text
|epsilon_(q,A)(M,L)| < 21*(k+1)/(5*q^2).
```

This `proof sketch` is cleaner than keeping the endpoint coboundary and the
temporal index shift separate: the fine child is evaluated at the literal
predecessor point `x_n`, and the parent at its suffix `x_(n+1)`.  It is still
universal decimal-orbit algebra, not a source of π sign.  Exact reconstruction
of the routed ten-vector requires its zero mode `R_0` together with the five
real nonzero character blocks; pairing is an isomorphism, not cancellation.

Two narrow separators locate the remaining failure.

- The total child flux is already negative at normalized radius `y=3/8` for
  every `q>=1000`; its asymptotic boundary is `1/(2*sqrt(2))`.  Thus the
  proved `|y|<=0.35` sibling-payment core is close to maximal and cannot be
  extended through the full cylinder.
- For the periodic replacement orbit `xi=1/9`, let `q_k=10^k` and
  `A_k=(q_k-10)/9`.  These form coherent digit-`1` extensions.  The carry
  router always selects child `1`, the normalized routed radius is `11/18`,
  and every orbit-generalized primitive endpoint vanishes.  For `m>=3`,
  `-Phi_m(11/18)>1/26`; hence over the fresh block the routed contribution to
  `D_1/q_k` is `<-45*q_k/26`, while every DFT magnitude is `>9*q_k/26`.
  Routed shell mass can therefore remain principal-sized, coherent, and
  adversely oriented at every scale.  This separator has no positive-parent
  premise and is not a counterexample to a π-specific transport theorem.

At the hard actual-π node `(10000,1334)`, the two old central suffixes have
literal predecessors `2` and `8`, while the fresh central occurrence and
unique FMR witness are in child `5` (`experiment`).  Central zero-mode support
therefore does not align the same child even where the full score succeeds.

The remaining robust rung must control the complete routed core **and** the
retained ancestor/parent suffix kernels with a per-scale same-child margin.
Summable endpoint and non-routed errors alone cannot supply that margin.

## Actual-pi central-return side lemma

The following strengthening is an independently audited `proof sketch`. It
is genuine pointwise information about the actual decimal orbit, but its
child is selected after the return and therefore it is not signed horizon
transport.

Let `alpha_m` be the exact zero coefficient, put

```text
mu_q = 10*alpha_(10q)-alpha_q,
M_q  = sum_(1<=g<2q) (10*gamma_(10q)(10g)-gamma_q(g)),
Delta_q = 100*(1-cos(pi/(10q)))-(1-cos(pi/q)).
```

The T128 closed zero coefficient and T172 closed defect mass give exactly

```text
mu_q + 2*M_q = q^2*Delta_q.                       (ZF)
```

For `q>=1000`, T172's positivity and bounds imply

```text
-mu_q/2 + 21/(10q^2) > 1/(20q^2).
```

Thus the scalar channel in the block carrier recurrence is strictly
favourable. This identity is universal coefficient algebra, not pi-specific
arithmetic.

Now let `x_n={10^n*pi}`. If an orbit segment avoids
`[1/11,10/11]`, it cannot switch between the two complementary chambers; its
corresponding decimal block consists entirely of zeroes or entirely of
nines. Avoidance on `[s,s+L)` therefore gives an integer `p` with

```text
0 < |pi-p/10^s| < 10^(-(s+L)).
```

Consequently every `nu>mu(pi)` gives, for all sufficiently large `s`, a
return `x_m in [1/11,10/11]` with `s<=m<ceil(nu*s)`. The
[Zeilberger--Zudilin bound](https://arxiv.org/abs/1912.06345)
`mu(pi)<=7.103205334137...` permits `nu=7.11`.

At such a return choose the literal values

```text
A=floor(q*x_(n+1)),   d=floor(10*x_n),   m=n+k+1,   q=10^k.
```

The common normalized carrier radius is `x_m-1/2`. The factorization above,
elementary sinc bounds, (ZF), and the audited endpoint error give

```text
C_(q,A,d)(n,1) > 607479/1250000 > 4859/10000.
```

Taking `s=q+k+1` shows that for every sufficiently large `k`, some
`q<=n<8q` has this complete literal relative gain. All digit-character
sectors and the parent-suffix kernel remain present.

The first fatal line is exact: the return chooses `A,d` after seeing the
orbit point, while T189 needs the child of a prescribed recursively reached
target. Moreover `C>0` is only child-minus-parent gain; it implies neither
`D_d>0` nor `G_d+D_d>0`, and left-extension stacking shifts the controlled
occurrence from `n` to `n-1`. A diagonal use of infinitely many central
times produces an unanchored coherent reversed-digit ray with recurrent
positive atoms, but loses the certified `334` seed and natural horizons.

## Central primitive atom and signed unit-block ladder

An independently audited strengthening repairs the missing total sign and
the lag mismatch at **unit-block** scale. T192 now machine-checks the atom and
shell identities below. For

```text
p_(q,A)(n) = Re(P_(q,A)(n+1)-P_(q,A)(n)),
y = q*(x_n-c_(q,A)),
```

where `P` is `primitiveBoundaryFourierSum`, let `L_s` be the positive
boundary polynomial restricted to frequencies divisible by `10^s`.  Exact
valuation shells are differences, not divisibility layers:

```text
H_s = L_s(x_n-10^s*c_(q,A))
      -L_(s+1)(10*x_n-10^(s+1)*c_(q,A)),
p_(q,A)(n) = sum_(0<=s<=k) Re H_s,       q=10^k.
```

If `A=floor(q*x_n)` and `|y|<=9/22`, machine-checked T191 supplies the central
kernel floor, and machine-checked T192 combines the root-grid projector with
the exact zero shell to give

```text
Re H_0 >= (9/20)*Phi_q(y),       Phi_q(y)>4859/10000.
```

The `Phi_q` floor, atom identity, shell partition, `H_s=L_s-L_(s+1)` identity,
displayed `H_0` retention, positive-valuation aggregate, full atom bound and
unit-block surplus are machine-checked. T194 additionally machine-checks an
unprescribed actual-pi return at every decimal scale under the explicit
external premise `IrrationalityMeasureBelow pi (36/5)`. The premise remains a
literature-checked external hypothesis. After a premise-dependent onset, T194
also machine-checks that one such positive unit lies in the exact fresh block
`q<=n<10q`. Only the infinite-ray and full-block deductions remain `proof
sketch`.

Machine-checked T193 applies the T151 floors to `L_1,L_2`, mass bounds to the
remaining layers, and the endpoint budget to give

```text
sum_(1<=s<=k) Re H_s > -108019/1800000,
p_(q,A)(n) > 7139/45000.
```

Consequently, for the T176 signed block capital

```text
S_(q,A)(M,L)
 = q*Re(primitiveBoundaryFourierBlockSum(q,A,M,L))-7*L/(3q),
```

machine-checked T193 gives `S_(q,A)(n,1)>3q/20` for `q>=1000`. Conditional
machine-checked T194 proves that the explicit premise
`IrrationalityMeasureBelow pi (36/5)` supplies some such literal actual-pi
root at every decimal scale and, eventually, one with `q<=n<10q`. This does
not sign the sum over the whole fresh block. Recursive T176 Bellman choices at
the unchanged block `(M,L)=(n,1)` then construct a coherent target ray with

```text
0 < S_(q_0,A_0)(n,1) < S_(q_1,A_1)(n,1) < ...,
q_(r+1)=10*q_r,       A_(r+1)=A_r+d_r*q_r.
```

Only the root target is literal; later Bellman children need not contain
`x_n`.  A diagonal pigeonhole argument further gives one fixed ray for which
every finite depth recurs at some depth-dependent time `n_R`.  It does not
give one common time or a positive prefix.

This is material signed intermediate progress but not prescribed-target
arithmetic or T189 FMR.  The periodic orbit `xi=1/9` satisfies the same
central atom and unit-block ladder at every time.  The first fatal line is
therefore exact: no result controls the intervening unit blocks needed to
deduce `S_(q_r,A_r)(0,q_r)>0`.  Reopen this rung only with a quantitative
actual-pi accumulation theorem that fails on `1/9` and on sparse
finite-prefix continuations.

## Exact carrier/remainder split

T174 splits each normalized signed surplus exactly into positive cylinder
mass, negative-lobe mass, primitive-shift endpoint, zero coefficient, and the
registered potential.  Applying that split separately to parent, old-child,
and fresh-child windows yields exact core vectors

```text
g_d^circ, d_d^circ, f_d^circ=g_d^circ+d_d^circ
```

built from positive cylinder masses and exact zero/potential terms, plus
signed remainder vectors `a_d,b_d,c_d` containing negative lobes and
endpoints.  For the **actual** sign sets

```text
P={d:D_d>0 and F_d>0},
O={d:D_d*F_d<0},
```

one obtains exactly

```text
J0/q^2 = Jcirc-C,

Jcirc=sum_(d in P) d_d^circ*f_d^circ
      -(1/4)*sum_(d in O)(g_d^circ)^2.
```

Here `C` is the explicit expansion remainder from the negative-lobe and
endpoint vectors.  It is signed, not universally a nonnegative flux.  Also,
`Jcirc` is not determined by positive occurrences alone because its index sets
`P,O` come from the complete actual scores.

## Hard-node result and exact remaining boundary

At `(q,A)=(10000,1334)`, the pinned π prefix has exactly two old parent
occurrences, with normalized radii in `(0.2574,0.2575)` and
`(0.1776,0.1777)`, and the unique relevant fresh child-`5` occurrence has
radius in `(-0.0977,-0.0976)`.  All lie in the sibling-payment region.  The
existing outward replay supplies the actual sign sets `P={5}`, `O={8}`.
Independent recomputation gives

```text
Jcirc ~= 55.600526,
```

and conservative analytic bounds support `Jcirc>54.4563`.  Because the
endpoint monotonicity used in those conservative substitutions was not itself
certified by a directed evaluator, retain the numerical statement as an
`experiment`, not a theorem.  The actual value satisfies

```text
J0/q^2 ~= 17.27272354,
C ~= 38.32780002.
```

The new carrier mechanism therefore explains a large positive core at the
hard node; accumulated target-specific annular mass and primitive endpoints
consume most of it.

At a fixed node the exact remaining inequality is `Jcirc>C`.  An all-scale
route must additionally construct the growing-horizon path, prove recurring
`Jcirc>0`, control the changing sign sets, and eventually supply word
coverage.  Reopen this route only with an actual-π weighted near-miss and
endpoint theorem strong enough for those literal recursively reached targets;
further kernel algebra or generic occupancy is not progress.
