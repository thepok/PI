# T130: decimal collision to S-unit audit

Audit date: 2026-08-10 UTC.

Statements attributed to S1-S5 and localized in `SOURCE_PINS.md` are
`literature-checked`. The collision algebra, theorem substitutions, transfer
tests, and comparisons below are `proof sketch` deductions. The replay is an
`experiment`: it checks hashes, source anchors, exact finite identities, and
report invariants, but is not evidence for an asymptotic assertion.

```text
PRIMARY_SOURCE_COUNT: 5
PRIMARY_SOURCE_CAP: 8
RETAINED_CANDIDATE_COUNT: 3
RETAINED_CANDIDATE_CAP: 3
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable statement, scope, and ambiguities

The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It records a local formulation dated 2026-07-22 and no external original
Erdos Problems URL. For integers `n,N>=1`, the canonical quantity is

```text
Q_pi(n,N)=#{(i,j) in {0,...,N-1}^2:
             ||(10^i-10^j)pi||_(R/Z)<10^(-n)}.
```

Pairs are ordered, all `N` diagonal pairs are included, and the inequality is
strict. The exact open quantifier order is

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N=N(A,n)>=1 with
                         A*n*Q_pi(n,N)<=N^2.
```

T130 does not alter or answer this question. It audits exact equal decimal
blocks, the T7 cylinder statistic which is machine-checked to be within a
factor three of `Q_pi`. The following conventions remove the agenda's
ambiguities.

1. `m` is block depth; canonical `n` is reserved for the statement above.
2. The audit scale is literally `m=floor(kappa*log_10 N)`, where `kappa>0`
   is fixed before `N` tends to infinity. No natural-log reinterpretation is
   used.
3. Starts alone satisfy `0<=i,j<N`. A block reads through endpoints `i+m`
   and `j+m`, which may exceed `N-1` and can be as large as `N+m-1`.
4. Decimal cylinders are left-closed and right-open. Leading zeroes remain in
   the fixed-width block integer. Irrationality of pi excludes grid endpoints.
5. Every collision count is ordered and diagonal-inclusive. An unordered or
   diagonal-free statistic is not substituted.
6. Overlap means `0<|i-j|<m`; it is not identified with S-unit degeneracy.
7. "S-unit equation" is used in two senses that are kept separate: rational
   units for a finite prime set `S`, and elements of one common finite-rank
   multiplicative group over a characteristic-zero field. The source rank is
   torsion-free group rank, not the number of equation terms or cylinders.
8. A theorem counting distinct group-valued solutions does not automatically
   count ordered index pairs; injectivity or a multiplicity bound is required.
9. In source theorems the arity is denoted `d` below, avoiding collision with
   canonical depth `n` and block depth `m`.
10. Prior reports are fingerprint comparators, not primary sources and not
    discharged premises. Reports under `notes/` remain unverified where their
    own labels say `proof sketch`.

## 2. Exact T7 starting point

The vendored `T7FiniteCylinderEnergy.lean` is byte-identical to the accepted
library module. Its relevant machine-checked interfaces are:

```text
piCylinderCollisionEnergy_eq_equalPairs_card       lines 126-150
normalizedPiCylinderCollisionEnergy_eq_equalPairs_card_div
                                                    lines 152-158
diagonal_le_piCylinderCollisionEnergy               lines 173-187
piCylinderCollisionEnergy_le_Q_pi_le_three_mul      lines 292-318
canonical_C1_iff_piFiniteCylinderEnergyFrontier     lines 346-386
```

Thus T7's energy is literally the cardinality of an ordered pair set, includes
all diagonal pairs, and obeys

```text
E_pi(m,N) <= Q_pi(m,N) <= 3*E_pi(m,N).               (2.1)
```

T7 proves this interface, not decay for the prescribed point.

Write

```text
q=10^m,
P_t=floor(10^t*pi),
y_t={10^t*pi}=10^t*pi-P_t,
B_(t,m)=floor(q*y_t)=P_(t+m)-q*P_t.                  (2.2)
```

Here `0<y_t<1`, and `B_(t,m)` lies in `{0,...,q-1}`. For each block integer
`B`, let

```text
c_B=#{0<=t<N:B_(t,m)=B}.                             (2.3)
```

Then the exact T7 convention is

```text
E_pi(m,N)=sum_(0<=B<q)c_B^2
         =#{(i,j) in {0,...,N-1}^2:B_(i,m)=B_(j,m)}. (2.4)
```

In particular, the diagonal contribution is exactly `N`, not an error term.

## 3. Collision-to-unit-equation ledger

Fix one collision `B_(i,m)=B_(j,m)=B`. Every start satisfies

```text
P_(t+m)=q*P_t+B,                                      (3.1)
y_(t+m)=q*y_t-B.                                      (3.2)
```

Subtracting the two copies gives the exact integer and fractional equations

```text
P_(i+m)-P_(j+m)-q*P_i+q*P_j=0,                       (3.3)
q*y_i-y_(i+m)-q*y_j+y_(j+m)=0.                       (3.4)
```

Equivalently,

```text
P_(i+m)-P_(j+m)=q(P_i-P_j),
y_(i+m)-y_(j+m)=q(y_i-y_j).                           (3.5)
```

Substitution of `P_t+y_t=10^t*pi` into (3.3) cancels pi identically. The
four-term relation therefore retains no hidden linear form in pi.

### 3.1 Coefficients, endpoints, and height

The coefficient vector in (3.3) is `(1,-1,-q,q)`. Its projective multiplicative
height is `q` and logarithmic height is `m*log 10`. The endpoint-index set is

```text
T_(N,m)={0,...,N-1} union {m,...,N+m-1},
|T_(N,m)|=N+min(m,N).                                  (3.6)
```

Since `3*10^t<=P_t<4*10^t`, every prefix endpoint has

```text
P_t<4*10^(N+m-1).                                      (3.7)
```

After normalizing (3.3) by `qP_j`, put

```text
U=P_(i+m), V=P_(j+m), S=qP_i, T=qP_j.
```

The inhomogeneous equation is

```text
V/T+S/T-U/T=1.                                         (3.8)
```

Its displayed coefficients have height one, while each ratio has height at
most `4*10^(N+m-1)`. Moving `q` into the variables does not remove its
contribution to the multiplicative group.

For a fixed nonzero block `B`, one start gives the simpler equation

```text
P_(t+m)/B-qP_t/B=1.                                    (3.9)
```

The map `t |-> (P_(t+m)/B,-qP_t/B)` is injective because `P_t` is strictly
increasing. Equation (3.9), not (3.8), is the clean two-variable occupancy
encoding.

### 3.2 Complete proper-subsum audit

The signed terms of (3.3) are `U,-V,-S,T`, with

```text
U-S=B,       -V+T=-B.                                  (3.10)
```

All six two-term subsums have the following status:

```text
U-V=0       iff i=j,
-S+T=0      iff i=j,
U-S=0       iff B=0,
-V+T=0      iff B=0,
U+T         is strictly positive,
-V-S        is strictly negative.                      (3.11)
```

No singleton vanishes. A three-term subsum cannot vanish because its
complementary singleton is nonzero. Therefore

```text
(3.3) is nondegenerate exactly when i!=j and B>0.       (3.12)
```

The same classification holds for (3.4): all `y_t` are nonzero, and the two
distinguished subsums equal `B` and `-B`. Equation (3.9) is nondegenerate for
every `B>0`; division by `B` is impossible for the zero block. Diagonal pairs
and every zero-block pair are outside the nondegenerate source counts.

### 3.3 Overlap is a separate endpoint issue

For `i<j`, put `d=j-i`. The blocks overlap iff `d<m`. All possible ordered
off-diagonal overlapping pairs, whether or not they collide, number exactly at
most

```text
C_overlap(N,m)=2*D*N-D*(D+1),
D=min(m-1,N-1).                                         (3.13)
```

For an overlapping collision define

```text
A=P_(i+d)-10^d*P_i,
A'=P_(i+m+d)-10^d*P_(i+m).
```

Computing the endpoint by the two paths gives

```text
q*A-(10^d-1)*B-A'=0.                                   (3.14)
```

If `m=a*d+r`, `0<=r<d`, and `C` is the integer represented by the first `r`
digits of the `d`-digit word `A`, then the exact repetition and endpoint rules
are

```text
B=A*sum_(h=0)^(a-1)10^(r+h*d)+C,                       (3.15)
A=10^(d-r)C+D0,  A'=10^r*D0+C             when r>0,   (3.16)
C=0,              A'=A                     when r=0.   (3.17)
```

For `B>0`, equation (3.14) is nondegenerate; for `B=0`, periodicity forces
`A=A'=0`. Thus overlap is not itself the degeneracy. It is cheap because
(3.13) is small at logarithmic depth; separated zero-block collisions remain
the unhandled family.

### 3.4 Common finite-rank group and its honest rank

For fixed `N,m`, define the scalar rational group

```text
G_(N,m)=<10, P_t:t in T_(N,m)> in Q^*,
R_(N,m)=rank G_(N,m).                                   (3.18)
```

The only unconditional generator count is

```text
R_(N,m)<=N+min(m,N)+1.                                  (3.19)
```

For each fixed `B>0`, adjoining `B` gives rank at most `R_(N,m)+1`, and
the product group containing all points in (3.9) has rank at most
`2(R_(N,m)+1)`. The three coordinates in (3.8) lie in `G_(N,m)^3`, of rank at
most `3R_(N,m)`. No multiplicative relation among the prefix integers is known
which lowers these ranks to `O(m)`.

Equivalently, for each finite instance one can put `2,5` and every prime
dividing these prefix integers into a finite set `S_(N,m)`. Equation (3.8) is
then a rational `S_(N,m)`-unit equation. For fixed `B>0`, equation (3.9) is an
`S_(N,m,B)`-unit equation only after adjoining every prime dividing `B`.
These prime sets grow with `N` and, for (3.9), with the selected block;
selecting a separate low-rank group for each collision cannot count a whole
fiber. The fractional terms in (3.4) lie in `Q(pi)`, a transcendental function
field rather than a number field, although characteristic-zero finite-rank
group theorems can formally apply after one common group is proved.

## 4. Every logarithmic-depth substitution

Fix `kappa>0` and set

```text
m=floor(kappa*log_10 N).                                (4.1)
```

For all sufficiently large `N`, `1<=m<N`, and exactly

```text
kappa*log_10 N-1 < m <= kappa*log_10 N,
N^kappa/10 < q=10^m <= N^kappa.                         (4.2)
```

Equations (3.6)-(3.7), (3.13), and (3.19) become

```text
|T_(N,m)|=N+m<=N+kappa*log_10 N,                        (4.3)
R_(N,m)<=N+kappa*log_10 N+1,                            (4.4)
H_coeff=q<=N^kappa,  h_coeff<=kappa*log N,              (4.5)
H_endpoint<4*10^(N-1)*N^kappa,                          (4.6)
h_endpoint<(N-1)log 10+kappa*log N+log 4,               (4.7)
C_overlap=2N(m-1)-m(m-1)
         =2*kappa*N*log_10 N+O_kappa(N+(log N)^2).      (4.8)
```

The diagonal plus every possible overlap pair is therefore
`O_kappa(N log N)`. After multiplication by `m` it contributes
`O_kappa(N(log N)^2)=o(N^2)`. This disposes of overlap without a theorem, but
does not bound disjoint positive-block fibers or the zero-block fiber.

The pigeonhole lower bounds, useful only as calibration, are

```text
E_pi(m,N)>=N,
E_pi(m,N)>=N^2/q>=N^(2-kappa).                           (4.9)
```

## 5. Candidate C1: Beukers-Schlickewei two-term count

### 5.1 Exact sourced theorem

S1, Theorem 1.1, printed p.189, PDF p.1, fixes the `Q`-closure `G` of a
finitely generated rank-`r` subgroup of `(C^*)^2` and proves that

```text
x+y=1, (x,y) in G
```

has at most

```text
2^(8r+8)                                                 (5.1)
```

solutions. The `Q`-closure consists exactly of points some positive power of
which belongs to the original group. Since both coordinates are nonzero,
two-term solutions are automatically nondegenerate. The rank is the
torsion-free rank of the subgroup of the product, not twice a scalar rank by
definition; twice the scalar rank is only the safe ambient bound used below.

### 5.2 Literal application and complete substitution

For fixed `B>0`, apply S1 to the injective points in (3.9). The ambient product
group rank is at most `2(R_(N,m)+1)`, so

```text
c_B<=M_BS(N,m):=2^(16*R_(N,m)+24).                      (5.2)
```

Summing squared occupancies gives only

```text
E_pi(m,N)<=c_0^2+M_BS(N,m)*(N-c_0),                     (5.3)
```

where `c_0` is the zero-block occupancy and is not controlled by S1.

Using every bound in (4.1)-(4.4), the auditable common-group certificate is

```text
M_BS(N,m)
 <=2^(16*(N+kappa*log_10 N+1)+24)
 =2^(16N+40)*N^(16*kappa*log_10 2).                     (5.4)
```

The polynomial exponent is

```text
16*kappa*log_10 2 = 4.8164799306...*kappa,              (5.5)
```

but the decisive factor is `2^(16N)`. The right side of (5.4) exceeds the
trivial fiber cap `N`, so (5.3) reduces to `E_pi<=N^2` even if `c_0=0`.

CHEAP_REJECTION_C1: insert the common generator count (4.4) into (5.1). The
result (5.4) is already worse than `c_B<=N`, and `B=0` is excluded. No height
estimate can repair a theorem whose bound depends only on this growing rank.

Card result: reject the available application at common-group rank and
zero-block degeneracy. S1 remains a viable related-model mechanism if an
independent logarithmic-rank theorem is supplied.

## 6. Candidate C2: Amoroso-Viada three-term count

### 6.1 Exact sourced theorem

S2, Theorem 6.2 and equation (6.24), printed p.26, PDF p.27, assumes an
algebraically closed characteristic-zero field `K`, nonzero fixed coefficients
`a_1,...,a_d`, and a subgroup `Gamma` of `(K^*)^d` of finite rank `r`. It
proves that

```text
a_1*x_1+...+a_d*x_d=1, x in Gamma
```

has at most

```text
A(d,r)=(8d)^(4*d^4*(d+r+1))                              (6.1)
```

nondegenerate solutions. The source defines nondegenerate to mean that no
nonempty subsum of the left side vanishes.

### 6.2 Literal application and complete substitution

Equation (3.8) has `d=3`, coefficients `(1,1,-1)`, and lies in
`G_(N,m)^3`, whose rank is at most `3R_(N,m)`. Even granting, optimistically,
that distinct ordered collisions give distinct triples, S2 gives at most

```text
M_AV(N,m)=24^(324*(3R_(N,m)+4))                           (6.2)
```

positive-block off-diagonal triples. Equations (3.11)-(3.12) show exactly why
the diagonal and every zero-block pair are absent.

The logarithmic-depth replacement (4.4) yields

```text
M_AV(N,m)
 <=24^(324*(3N+3*kappa*log_10 N+7))
 =24^(972N+2268)*N^(972*kappa*log_10 24).                (6.3)
```

The polynomial exponent is

```text
972*kappa*log_10 24 = 1341.565...*kappa,                 (6.4)
```

in addition to the exponential factor `24^(972N)`. This exceeds the entire
ordered-pair universe `N^2`.

There is also a logically prior multiplicity gap. The map

```text
(i,j) |-> (P_(j+m)/(qP_j), P_i/P_j, P_(i+m)/(qP_j))      (6.5)
```

has not been proved injective; S2 counts distinct triples, not representations
by ordered pairs. The optimistic calculation (6.3) therefore gives the card
more than is currently justified and still fails.

CHEAP_REJECTION_C2: grant injectivity and delete all degenerate collisions,
then insert `d=3` and (4.4) into the exact sourced constant. Formula (6.3) is
already larger than `N^2`; restoring multiplicity and degeneracy only worsens
the application.

Card result: reject at growing rank, ordered-pair multiplicity, and degenerate
subsum coverage.

## 7. Candidate C3: Bugeaud-Evertse block complexity

### 7.1 Exact sourced theorem

S3 defines, on PDF p.1, the global block complexity

```text
p(d,xi,b)=#{length-d blocks occurring anywhere in the b-ary expansion of xi}.
```

Theorem 2.1 and equation (2.2), printed p.223, PDF p.3, assume integer `b>=2`
and an algebraic irrational real `0<xi<1`. For every real `eta<1/11`, they
prove

```text
limsup_(d->infinity) p(d,xi,b)/(d*(log d)^eta)=infinity. (7.1)
```

This is a global support-size lower bound along a subsequence. It is not a
prefix frequency theorem, an upper collision estimate, or a theorem about the
transcendental number pi.

### 7.2 Complete logarithmic-depth substitution

For integers `N` satisfying `m=floor(kappa*log_10 N)`, (7.1) becomes only the
subsequential related-model statement

```text
limsup p(m,xi,10)/
 [floor(kappa*log_10 N)*(log floor(kappa*log_10 N))^eta]
 =infinity,                                               (7.2)
```

along a choice of `N` realizing the sourced depths. In scale notation its
denominator is

```text
kappa*log_10 N*(log(kappa*log_10 N))^eta*(1+o(1)).        (7.3)
```

No explicit threshold or lower multiplier is sourced.

More importantly, support does not control squared multiplicity. For any
`1<=p<=N`, occupancies

```text
N-p+1,1,1,...,1
```

on exactly `p` words have ordered diagonal-inclusive energy

```text
E_concentrated(N,p)=(N-p+1)^2+p-1.                       (7.4)
```

If `p=o(N)`, then (7.4) is `(1-o(1))*N^2`. Thus even an unbounded multiple of
the polylogarithmic quantity in (7.3) supplies no upper bound of order
`o(N^2/m)`. Cauchy-Schwarz uses support in the opposite direction:
`E>=N^2/p`.

CHEAP_REJECTION_C3: substitute any sourced support value `p` into (7.4). The
same support is compatible with energy asymptotic to `N^2`; the theorem's
algebraicity hypothesis also excludes pi. This rejects the collision-energy
application without disputing the source theorem.

Card result: reject as support rather than frequency control, with an
additional object mismatch at pi.

## 8. Fourth source screened, not retained

S4, Fischler-Rivoal Theorem 3, PDF pp.5 and 15, considers a nonrational
G-function with rational Taylor coefficients, fixed `epsilon>0`, nonzero
integer `a`, base `b>=2`, and an integer `s` for which `b^s` is sufficiently
large in terms of `F,epsilon,a`. For every fixed pattern length `t>=1`, it
proves

```text
limsup_(n->infinity) N_b(F(a/b^s),t,n)/n <= epsilon/t,    (8.1)
```

where `N_b` counts consecutive powers of the one length-`t` pattern starting
at digit `n`. For `Li_2(1/b^s)` the displayed sufficient calibration is
`s>=10^7/epsilon`; the proof uses the restricted denominator
`b^(n-1)(b^t-1)`.

This source is not a fourth candidate. It controls one contiguous repetition
at one start, not arbitrary equal blocks at two starts. Setting
`t=m=floor(kappa*log_10 N)` changes the fixed theorem parameter with `N`; no
uniform threshold in growing `t` is stated. Even a uniform version would touch
only overlapping/periodic repetitions, whose entire ordered population is
already bounded by (4.8), and its G-value hypotheses do not specialize to pi.

## 9. Candidate comparison and conditional thresholds

| Card | Equation/object | Sourced count | Available rank/support at `m=floor(kappa log_10 N)` | First failed certificate |
|---|---|---|---|---|
| C1 S1 | fixed positive-block equation (3.9), injective starts | `2^(8r+8)` | product rank `<=2(N+m+2)` | (5.4) exceeds `N`; zero block excluded |
| C2 S2 | normalized collision triple (3.8) | `24^(324(r+4))` at `d=3` | rank `<=3(N+m+1)` | (6.3) exceeds `N^2`; pair-to-tuple multiplicity and degeneracy remain |
| C3 S3 | global distinct-block support | limsup lower bound (7.1) | denominator only polylogarithmic in `N` | concentrated occupancy (7.4) has energy near `N^2` |

The rank thresholds clarify what would be needed in a related model. If the
actual product-group rank in C1 were bounded by `rho*m+r0`, then

```text
2^(8r+8)
 <=2^(8r0+8)*N^(8*rho*kappa*log_10 2).                  (9.1)
```

To make this `o(N/m)` and hence make the summed positive-block energy
`o(N^2/m)`, the strict numerical condition is

```text
8*rho*kappa*log_10 2<1,
rho*kappa<1/(8*log_10 2)=0.415241... .                  (9.2)
```

If C2 had an injective encoding and direct triple-group rank `rho*m+r0`, then

```text
A(3,r)=24^(324*(r+4))
       =O(N^(324*rho*kappa*log_10 24)).                  (9.3)
```

To make the total positive off-diagonal count `o(N^2/m)` requires

```text
324*rho*kappa*log_10 24<2,
rho*kappa<2/(324*log_10 24)=0.004472... .                (9.4)
```

These are conditional calibration inequalities, not rank assertions.

## 10. Required fingerprint comparisons

Every readable comparator is vendored byte-exactly. Its verification level is
part of the comparison; no proof-sketch claim is used as a premise.

| Comparator | Level and normalized fingerprint | T130 separator |
|---|---|---|
| T81 | `prior-t81-REPORT.md`; overall `proof sketch`, with machine-checked T73/T28 interfaces and one pinned pi irrationality source. It packs many scalar approximations at exponential coefficient height and finds no cross-numerator compatibility. | T130 counts exact finite-rank-group solutions rather than separating scalar phases. Its available common rank is linear in `N`, reproducing T81's exponential-capacity obstruction in group-rank form; it does not claim T28 compatibility. |
| T87 | `prior-t87-REPORT.md`; four source statements `literature-checked`, restricted Bugeaud-Kim localization and cross-program deductions `proof sketch`. Its repetition denominator is `10^u(10^v-1)` and the needed restricted exponent is below `2.246979...`; available ordinary pi bounds miss it. | S4 independently recovers the same restricted repetition-denominator shape for one G-value run. T130's C1-C2 instead use exact prefix-integer groups, while C3 fails support-to-frequency; no restricted fixed-pi exponent is recycled. |
| T114 | `prior-t114-REPORT.md`; eight sources `literature-checked`, determinant transfers `proof sketch`. Its homogeneous interpolation determinant pays height `10^N`, loses rational rank, and does not aggregate fixed-lag recurrence. | Equation (3.3) is an exact additive prefix identity, not T114's near-integer determinant. Moving prefix integers into a multiplicative group avoids determinant height but makes rank `N+O(log N)`; this is a distinct, explicitly quantified obstruction. |
| T119 | `prior-t119-REPORT.md`; recovered revised report, source statements self-labeled `literature-checked`, translations `proof sketch`, replay `experiment`; its source PDFs and verifier are absent from this snapshot, so those checks are not rerunnable here. It rejects collision concentration implying predictive/Hankel/Prony rank. | T130's rank is torsion-free multiplicative-group rank of exact rational tuples, not matrix rank, automaton state, singular-value rank, or moment support. No inference from high collision to low predictive rank is made. |
| T125 | `prior-t125-REPORT.md`; accepted pinned literature artifact, with source statements `literature-checked` and Walsh/substitution deductions `proof sketch`. Its complete all-subset expansion needs correlations through growing order `m=floor(kappa log N)` and available theorems leave exponential subset mass. | T130 uses no correlation expansion. Its growing parameter is multiplicative rank, and the exact source constants fail after (5.4)/(6.3). Both routes expose growing complexity, but their equations and rejection tests are disjoint. |
| active T127 | The only supplied evidence is the active generation-1 lease in the T130 orchestration snapshot and the agenda phrase "active T127's agenda-level scout". No T127 report, source pin, theorem, title, or mathematical fingerprint is present in the knowledge library or staged records. Verification level: unavailable. | No content is inferred and no novelty or duplication claim is made against T127. T130 is compared only at the honest agenda boundary: it audits exact collision-to-S-unit equations. This row must be refreshed if T127 becomes readable before adjudication. |

The T119 recovered report is used only as unverified comparison memory because
its self-reported source package is incomplete here. Active T127 is weaker
still: an observation/lease is not evidence and cannot promote an inferred
fingerprint.

## 11. Non-circular pi-specific transfer premise

The following is a `conjecture` stated to expose the exact missing arithmetic
input. It is not asserted, and no inspected source supplies it.

**PI-SUNIT-RANK (conjectural transfer; not asserted).** There exist fixed
constants `kappa>0`, `rho>=0`, integer `r0>=0`, a sequence of integers
`N_m>=1`, a sequence of reals `epsilon_m>=0` with `epsilon_m->0`, and an exact
source-pinned family of nonzero generator pairs

```text
g_(m,B,l) in (C^*)^2,
m>=1, 1<=B<10^m, 1<=l<=ceil(rho*m)+r0,                  (11.0)
```

whose formulas depend only on `(m,B,l)` and a fixed exact arithmetic
representation of pi, and not on the set of starts whose blocks equal `B`,
such that

```text
8*rho*kappa*log_10 2<1,                                  (11.1)
```

and, for every sufficiently large integer depth `m`, the preselected `N_m`
satisfies `m=floor(kappa*log_10 N_m)` and both:

1. for every `B in {1,...,10^m-1}`, all exact points
   `(P_(t+m)/B,-10^m*P_t/B)` with `0<=t<N_m` and `B_(t,m)=B`
   lie in the `Q`-closure of one subgroup of `(C^*)^2` generated by at most
   `ceil(rho*m)+r0` of the predeclared pairs (11.0); and
2. the zero-block occupancy satisfies
   `#{t<N_m:B_(t,m)=0}<=epsilon_m*N_m/sqrt(m)`.

Clause 1 is a multiplicative-generation theorem about exact prefix integers,
not an assumed collision count. The demand that generator formulas be fixed
before collision inspection excludes a post-hoc list containing one generator
per observed start. Clause 2 is a separate zero-run estimate forced by the
exact degeneracy audit, not a hidden assertion about all cylinder energy.

Conditionally on PI-SUNIT-RANK, the ceiling changes (9.1) only by a fixed
factor, so S1 and (9.1)-(9.2) give

```text
max_(B>0)c_B=o(N_m/m).
```

Then

```text
E_pi(m,N_m)=c_0^2+sum_(B>0)c_B^2
 <=c_0^2+(max_(B>0)c_B)*N_m=o(N_m^2/m).                 (11.2)
```

Together with the machine-checked factor-three comparison (2.1), (11.2) would
be a conditional route to the canonical inequality. This paragraph is only a
`proof sketch` implication from an unproved conjectural premise; it establishes
no property of pi and no C1 or C2 claim.

**Cheap transfer test.** A proposed exact representation must print (11.0),
`N_m`, and `epsilon_m`. At any claimed post-threshold depth, compute the
torsion-free rank and the ratio `sqrt(m)*c_0/N_m`. Rank above
`ceil(rho*m)+r0`, failure of (11.1), a generator formula depending on the
observed collision fiber, or `sqrt(m)*c_0/N_m>epsilon_m` rejects that proposal
at that depth. The proposal must separately prove `epsilon_m->0`; passing
finitely many instances is only an `experiment`.

## 12. Replay and endpoint

From a directory containing only the delivered artifacts, run

```text
python3 verify_t130.py
sha256sum -c SHA256SUMS
```

The verifier checks all canonical, source, T7, and comparator hashes; converts
the five PDFs afresh with `pdftotext -layout` and checks page-scoped theorem
anchors; checks the source and candidate caps; replays finite exact collision,
degeneracy, overlap, concentrated-support, and displayed numerical-constant
identities; and checks all six comparison rows, the transfer quantifiers, the
logarithmic-depth ledger markers, and the unique verdict/successor/non-claim
markers. Direct inspection of the displayed proof sketch remains necessary;
finite replay checks transcription and counterexample formulas only.

SCOPED_VERDICT (1/1): **CLOSE.** This closes only the audited fingerprint that
standard quantitative S-unit/Subspace-theorem counts, applied directly to
literal equal decimal blocks, presently bound ordered collision energy. The
two group-equation cards fail at the available `N+O(log N)` rank and degenerate
zero block; the three-term card also lacks ordered-pair injectivity; the
digit-complexity card controls support rather than multiplicity. Related-model
theorems remain results about their own groups, algebraic numbers, or G-values
and are not progress on fixed pi, C1, or C2. No bounded successor is proposed.
