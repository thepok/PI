# T134: single-cylinder zero-block occupancy audit

Audit date: 2026-08-10 UTC.

Statements attributed to S1--S6 and localized in `SOURCE_PINS.md` are
`literature-checked`. The collision identity, theorem substitutions, threshold
tests, and fingerprint comparisons below are `proof sketch` deductions. The
bounded replay is an `experiment`: it checks source pins, transcription,
finite identities, and displayed arithmetic, but it is not evidence for an
asymptotic or fixed-point assertion.

```text
PRIMARY_SOURCE_COUNT: 6
PRIMARY_SOURCE_CAP: 8
RETAINED_CANDIDATE_COUNT: 3
RETAINED_CANDIDATE_CAP: 3
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable statement, provenance, and normalized scope

The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It is the local question formulated by this system on 2026-07-22; no external
Erdos Problems URL is recorded. For integers `n,N>=1`, it defines

```text
Q_pi(n,N)=#{(i,j) in {0,...,N-1}^2:
             ||(10^i-10^j)pi||_(R/Z)<10^(-n)}.
```

Pairs are ordered, all `N` diagonal pairs are included, and the inequality is
strict. Its exact open quantifiers are

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N=N(A,n)>=1 with
                         A*n*Q_pi(n,N)<=N^2.
```

T134 neither changes nor answers this question. It audits one term in T7's
equal-decimal-cylinder energy. To prevent symbol collision, `m` denotes the
decimal depth in this report and canonical `n` is reserved for the statement
above.

The agenda ambiguities are normalized as follows.

1. A source is counted once although its PDF may be converted to text during
   replay.
2. A retained candidate is one theorem-application card, not one source or
   one parameter value. Retention permits rejection after substitution.
3. Decimal cylinders are left-closed and right-open. For irrational `x`, no
   orbit point is a decimal grid endpoint.
4. The cutoff restricts starts `0<=i<N`; a depth-`m` block may read digits
   through position `N+m-2`.
5. Every square counts ordered pairs and includes its diagonal.
6. `A,m,N` are positive integers. Any possible full T7 witness must have
   `N>=A*m`, because its energy and `Q` are both at least the `N` diagonal
   pairs.
7. A maximum-run theorem is not an occupancy theorem unless it also controls
   the number and placement of runs.
8. Almost-everywhere, invariant-measure, or existential-point results do not
   specialize to the prescribed point.
9. A source asymptotic with a fixed word length has no uniform growing-depth
   range unless the source supplies it.
10. Prior reports are fingerprint comparators, not discharged premises. T87
    and T113 are supplied under `notes/` and remain unverified proof-sketch
    memory outside their pinned source statements.

## 2. Exact zero-fiber identity and T7 budget

For real `x` and integers `m,N>=1`, define the decimal code and its occupancy
by

```text
C_m(x,i)=floor(10^m*{10^i*x}) in {0,...,10^m-1},
c_b(x;m,N)=#{0<=i<N:C_m(x,i)=b},
Z_m(x,N)=c_0(x;m,N).
```

The finite collision energy with T7's convention is

```text
E_x(m,N)=sum_(b=0)^(10^m-1)c_b(x;m,N)^2
        =#{(i,j) in {0,...,N-1}^2:C_m(x,i)=C_m(x,j)}.       (2.1)
```

The equality follows by partitioning the ordered pair set by its common code.
For the zero code specifically,

```text
#{(i,j):0<=i,j<N, C_m(x,i)=C_m(x,j)=0}
 =#{i:C_m(x,i)=0}*#{j:C_m(x,j)=0}
 =Z_m(x,N)^2.                                               (2.2)
```

This is an exact ordered contribution, not an upper bound or heuristic. The
vendored machine-checked T7 interface identifies the same squared-fiber sum
with ordered equal-code pairs and proves, only for the pi orbit,

```text
E_pi(m,N)<=Q_pi(m,N)<=3*E_pi(m,N).                          (2.3)
```

Consequently a sufficient full-energy budget for the canonical inequality at
parameters `A,m,N` is

```text
E_pi(m,N)<=N^2/(3*A*m).                                    (2.4)
```

T134 assigns half of (2.4) to the zero fiber and uses the agenda's exact screen

```text
Z_m(x,N)^2<=N^2/(6*A*m),                                   (T134-SCREEN)
```

equivalently

```text
Z_m(x,N)/N<=1/sqrt(6*A*m).                                 (2.5)
```

Since `E_x(m,N)>=N`, (2.4) itself requires `N>=3*A*m` under
this particular sufficient allocation; the weaker necessary canonical range
is `N>=A*m`. Every card is first tested against the agenda's required weaker
range `N>=A*m`, so no candidate is killed merely by the optional factor-three
allocation.

Most importantly,

```text
E_x(m,N)=Z_m(x,N)^2+sum_(b=1)^(10^m-1)c_b(x;m,N)^2.         (2.6)
```

Thus passing `T134-SCREEN` controls only one term. To combine it with (2.4),
one would still need the independent positive-cylinder budget

```text
sum_(b=1)^(10^m-1)c_b(pi;m,N)^2<=N^2/(6*A*m).              (2.7)
```

No candidate below proves (2.7).

## 3. Bounded source search and candidate freeze

The audit stopped after six primary papers in the three required lanes.

| Lane | Opened primary sources | Retained card |
|---|---|---|
| restricted-denominator approximation and avoidance | S1 Zeilberger--Zudilin; S2 Bugeaud--Kim; S3 Moshchevitin | C-RD uses S1--S2; S3 screened |
| explicit constants / G- and Mahler-function methods | S4 Fischler--Rivoal | C-GRUN |
| symbolic shrinking-target, run-length, and exact incidence | S5 Fishman--Merrill--Simmons; S6 Becher--Carton | C-DB uses S5; S6 screened |

The three retained cards are exactly `C-RD`, `C-GRUN`, and `C-DB`. S3 is not
a fourth card: its Theorem 2 gives nonemptiness of an avoidance set after
separate variable-`H` hypotheses, but no member, decimal expansion, or
prescribed-point specialization. This is the T113/T116 selection boundary.
S6 is not a fourth card because its nested-necklace discrepancy is the already
readable T121/T128/T131 global-incidence route, stronger than a one-fiber
mechanism.

No almost-everywhere theorem is retained. A theorem controlling only maximum
run length is retained only long enough to perform the mandatory kill
calculation in C-GRUN. No ineffective asymptotic is promoted to a finite
occupancy bound.

## 4. C-RD: rational approximation and repetition exponents

### 4.1 S1 theorem and exact zero-hit substitution

S1 defines the irrationality measure `mu(x)` on printed p.407 as the smallest
`M` such that, for every `eta>0` and all sufficiently large denominators `q`,

```text
|x-p/q|>q^(-(M+eta))                                       (4.1)
```

for every integer numerator `p`. Printed p.418 gives

```text
mu(pi)<=M_ZZ=7.1032053341370017275... .                    (4.2)
```

Suppose `i>=1` is counted by `Z_m(pi,N)` and put
`p_i=floor(10^i*pi)`, `q_i=10^i`. Irrationality makes the error positive, and
the zero-cylinder condition gives exactly

```text
0<pi-p_i/q_i<10^(-(i+m))=q_i^(-(1+m/i)).                  (4.3)
```

Fix `eta>0`. Once `q_i` is beyond the onset in (4.1), equations (4.1)--(4.3)
are incompatible whenever

```text
i<=m/(M_ZZ+eta-1).                                        (4.4)
```

Let `i0(eta)>=1` be the unspecified source onset in powers of ten and put
`L=floor(m/(M_ZZ+eta-1))`. The complete theorem-derived finite statement is
only

```text
Z_m(pi,N)
 <=N-max(0,min(N-1,L)-i0(eta)+1).                          (4.5)
```

No numerical `i0(eta)` is printed by the source. Even granting the favorable
fiction `i0=1`, and taking the agenda-compatible test `A=1,N=m`, (4.5) becomes

```text
Z_m(pi,m)<=m-floor(m/(M_ZZ+eta-1))
          =(1-1/(M_ZZ+eta-1)+o(1))*m,                     (4.6)
```

whereas `T134-SCREEN` requires

```text
Z_m(pi,m)<=sqrt(m/6).                                      (4.7)
```

The upper bound (4.6) is linear and therefore cannot certify (4.7). For
`N>>m` its ratio to `N` is even closer to one. This is a failure of the
available upper-bound application, not a lower bound on the actual occupancy.

### 4.2 S2 theorem and maximum-repetition kill

S2 Lemma 3.6, printed pp.944--945, assumes a non-ultimately-periodic base-`b`
word and proves

```text
mu(x)>=rep(word)/(rep(word)-1),                             (4.8)
```

using rational denominators
`b^|W|*(b^|UV|-1)`. It converts repeated prefixes into good restricted
approximations. It does not upper-bound the number of occurrences of `0^m` in
the first `N` starts.

Combining the sourced inequalities `mu(pi)<=M_ZZ` and (4.8), with the usual
decreasing interpretation of `r/(r-1)` for `r>1`, gives only

```text
rep(pi digits)>=rho_ZZ:=M_ZZ/(M_ZZ-1),
rho_ZZ-1=1/(M_ZZ-1)=0.163848... .                          (4.9)
```

Here `rep(word)=liminf r(m,word)/m`, where `r(m,word)` is the shortest prefix
containing two occurrences of some length-`m` factor. Fix any
`1<tau<rho_ZZ`. Formula (4.9) gives, for all sufficiently large `m`,

```text
r(m,pi digits)>=tau*m.                                     (4.10)
```

If two depth-`m` blocks among starts `0<=i<j<N` were equal, the prefix through
the second block would have length at most `N+m-1`, so
`r(m,pi digits)<=N+m-1`. Therefore (4.10) can certify uniqueness only in the
range

```text
N+m-1<tau*m,
N<(tau-1)*m+1<0.163849*m+1.                                (4.11)
```

For `A>=1`, the required range is `N>=A*m>=m`, which is disjoint from (4.11)
for all sufficiently large `m`. Beyond the first-repeat threshold, `rep`
supplies no multiplicity bound at all. Thus S2 cannot even certify
`Z_m(pi,N)<=1` in the agenda's admissible range, much less
`Z_m(pi,N)<=N/sqrt(6*A*m)`.

`CHEAP_KILL_C-RD`: insert the strongest favorable onset into (4.5) at
`A=1,N=m`; if the result remains linear while (4.7) is square-root, the theorem
does not certify the screen. For S2, compute
`rho_ZZ-1=1/(M_ZZ-1)` and compare the uniqueness ceiling (4.11) with
`N>=A*m`; the ranges are disjoint already at `A=1`.

Card result: reject. S1 excludes only an initial interval of possible starts;
S2 controls repetition exponents rather than zero-fiber multiplicity.

## 5. C-GRUN: explicit G-value run theorem

### 5.1 S4 theorem and source range

S4 defines `N_b(xi,t,n)` on PDF p.5 as the number of consecutive repetitions,
starting at digit `n`, of the length-`t` pattern beginning there. For `t=1`,
it is the length of the run of one equal digit starting at `n`. Theorem 3 on
the same page assumes a nonrational G-function with rational Taylor
coefficients, nonzero integer `a`, base `b>=2`, fixed `epsilon>0`, and an
integer `s` for which `b^s` is sufficiently large in terms of the data. It
proves, for every fixed `t>=1`,

```text
limsup_(n->infinity) N_b(F(a/b^s),t,n)/n<=epsilon/t.        (5.1)
```

For `Li_2(1/b^s)`, the source prints the explicit sufficient calibration

```text
s>=10^7/epsilon.                                           (5.2)
```

Section 4, PDF p.15, uses the restricted denominator
`b^(n-1)*(b^t-1)`. This is a theorem about the displayed G-values, not pi.

### 5.2 Every occupancy substitution

Fix one integer `s>2*10^7`, base `b=10`, and the fixed point

```text
xi_s=Li_2(10^(-s)),       theta=2*10^7/s in (0,1).          (5.3)
```

Apply S4 with source parameter `epsilon=theta/2=10^7/s` and `t=1`.
Condition (5.2) holds with equality. From the limsup statement, after an onset
depending on this fixed point, every equal-digit run starting at digit `n` has
length at most `theta*n`.

A start `i` counted by `Z_m(xi_s,N)` begins a zero run of length at least `m`
at digit `n=i+1`. Hence, after the source onset,

```text
m<=theta*(i+1),
i>=m/theta-1.                                               (5.4)
```

Even deleting the onset and endpoint errors favorably, (5.4) gives only

```text
Z_m(xi_s,N)<=max(0,N-ceil(m/theta)+1).                     (5.5)
```

Choose any fixed integer `A>1/theta` and the cheapest allowed cutoff `N=A*m`.
The right side of (5.5) is

```text
(A-1/theta)*m+O(1),                                        (5.6)
```

while `T134-SCREEN` requires

```text
Z_m(xi_s,A*m)<=sqrt(A*m/6).                                (5.7)
```

Again the theorem-derived cap is linear and does not certify the square-root
threshold. Taking a smaller `epsilon` in (5.1) requires increasing `s` in
(5.2), hence changes `xi_s`; it cannot establish the all-`A` property for one
fixed point. Taking `t=m` is also invalid as a uniform substitution because
S4 fixes `t` before the `n` limit and prints no onset uniform in growing `t`.

`CHEAP_KILL_C-GRUN`: for the proposed fixed `s`, set
`theta=2*10^7/s`, choose `A=floor(1/theta)+2`, and compare (5.6) with (5.7).
For all sufficiently large `m`, the source cap exceeds the required cap.

Card result: reject. The theorem controls maximum local run length at a
different fixed G-value, not the number of zero-block starts, and its explicit
parameter range cannot serve every `A` for one point.

## 6. C-DB: totally de Bruijn exact occupancy

### 6.1 S5 theorem and exact model

S5 definition (2.1), printed pp.3--4, defines a noncyclic order-`d` de Bruijn
word on a `k`-symbol alphabet to have length `k^d+d-1` and to contain every
length-`d` word exactly once. A totally de Bruijn infinite word has such an
initial prefix for every `d>=1`. Corollary 4.3 and its proof, printed
pp.10--11, prove the existence of totally de Bruijn expansions for alphabet
size `k>=4` by extending each order to the next; decimal `k=10` is in range.

Fix one such decimal word `omega` and its associated real `x_DB`. At an order
`d` endpoint put

```text
N=10^d.                                                     (6.1)
```

The source prefix has length `N+d-1`, so all starts `0<=i<N` are legal. For
every `1<=m<=d`, exactly `10^(d-m)` of the `10^d` distinct depth-`d` words
begin with `0^m`. Therefore

```text
Z_m(x_DB,10^d)=10^(d-m)=N/10^m,                            (6.2)
Z_m(x_DB,10^d)^2=N^2/10^(2*m).                             (6.3)
```

Substitution into `T134-SCREEN` is exact:

```text
N^2/10^(2*m)<=N^2/(6*A*m)
iff 6*A*m<=10^(2*m).                                       (6.4)
```

The required cutoff range is independently

```text
N=10^d>=A*m.                                               (6.5)
```

One completely explicit schedule is

```text
A>=1, m>=A, d=m, N=10^m.                                  (6.6)
```

Indeed `A*m<=m^2<=10^m=N` and
`6*A*m<=6*m^2<=10^(2*m)` for every integer `m>=1`. Thus C-DB
passes the one-fiber screen with every `A,m,N` range displayed.

### 6.2 Why the pass is not a new survivor

The pass uses exact balance of every depth-`m` word at a de Bruijn endpoint.
In fact, at `d=m`, every occupancy is one and the full model energy is `N`,
not merely a controlled zero term. This is the global incidence-balancing
mechanism already explicit in T111's FMS construction, T128's C-UG card, and
T131's C-NEST cycle-flow card. S6 Theorem 1 supplies another already-audited
version through nested perfect necklaces and `O((log N)^2/N)` discrepancy; it
is screened rather than renamed.

`CHEAP_KILL_C-DB-AS-NEW`: ask whether the sourced argument still proves (6.2)
after replacing the constructed de Bruijn point by the prescribed point while
retaining the same starts and endpoints. S5 has no such transfer theorem. If
one retains the constructed point, the card is exactly the prior global
incidence model; if one changes to pi, the premise is absent.

Card result: passes as an exact related model but closes as a disclosed
T111/T128/T131 duplicate. It proves no property of pi.

## 7. Candidate-specific prior and active comparison

Verification levels are part of every cell. The nine readable comparator
reports are byte-pinned inside `prior_evidence.tar`; none of their proof-sketch
deductions is used as a theorem premise.

| Comparator and level | C-RD | C-GRUN | C-DB |
|---|---|---|---|
| T87, unverified mixed-level note; sources literature-checked | `C-RD/T87`: same ordinary/restricted irrationality family; T134 specializes one zero hit and shows the resulting excluded-start interval misses occupancy scale | `C-GRUN/T87`: same restricted repetition-denominator shape, but at a G-value; no T10 or numerator-conductor claim is reused | `C-DB/T87`: exact symbolic incidence, no rational approximation, adaptive numerator, or fixed-pi sum |
| T111, sources literature-checked and deductions proof sketch | `C-RD/T111`: arithmetic lower approximation bounds do not construct T111's odd-digit nested word | `C-GRUN/T111`: local maximum runs do not give remote label separation | `C-DB/T111`: exact FMS source duplication; all ten symbols replace odd coding, and only zero occupancy is extracted |
| T113, unverified note; sources literature-checked | `C-RD/T113`: fixed-pi ordinary exponent versus T113's existential all-difference Moshchevitin point; no T113 deduction is imported | `C-GRUN/T113`: one explicit G-value and local runs, not variable-`H` avoidance | `C-DB/T113`: named symbolic model already acknowledged by T113, not its existential avoidance route |
| T116, sources literature-checked and deductions proof sketch | `C-RD/T116`: no weighted-game selector or safe interval | `C-GRUN/T116`: explicit point but no finite occupancy selector; the run theorem has the wrong statistic | `C-DB/T116`: repeats the FMS effective symbolic selector, not C-RS's dyadic avoidance tree |
| T119 recovered report, sources self-labeled literature-checked but package incomplete; comparison memory only | `C-RD/T119`: no predictive, Hankel, or moment rank inference | `C-GRUN/T119`: Mahler/G-function ancestry does not identify the unary coefficient Hankel matrix or all-start block matrix | `C-DB/T119`: exact incidence balance is direct, not inferred from low rank; one fiber does not imply a singular-value tail |
| T121, sources literature-checked and deductions proof sketch | `C-RD/T121`: one-sided rational hits, not aggregate Walsh/Legendre energy | `C-GRUN/T121`: maximum runs do not control the aggregate L2 statistic | `C-DB/T121`: zero fiber is one coordinate of T121's global incidence identity; the de Bruijn endpoint is an already-held exact model |
| T128, sources literature-checked and deductions proof sketch | `C-RD/T128`: retains the prescribed point but gives only an initial exclusion interval; T128 changes the point and obtains full discrepancy | `C-GRUN/T128`: nearest to the rejected Mahler/run-length lane; no growing-depth modulus or occupancy count | `C-DB/T128`: exactly C-UG's nested de Bruijn prefix calculation, restricted to word `0^m` |
| T130, sources literature-checked and deductions proof sketch | `C-RD/T130`: directly tests T130's excluded zero-block degeneracy but leaves almost all starts available | `C-GRUN/T130`: S4 was already screened there; T134 supplies the missing literal occupancy kill | `C-DB/T130`: controls the degenerate fiber in a constructed model but supplies no positive-block S-unit rank for pi |
| T131, sources literature-checked and deductions proof sketch | `C-RD/T131`: no circulation, Euler ordering, or nesting | `C-GRUN/T131`: local run asymptotics do not order a balanced flow | `C-DB/T131`: exact C-NEST incidence realization; no new cycle-space mechanism |
| active T132, no readable artifact or agenda fingerprint beyond its identifier | `C-RD/T132`: availability comparison only; no unpublished overlap or distinction inferred | `C-GRUN/T132`: availability comparison only | `C-DB/T132`: availability comparison only |
| active T133, no readable artifact or agenda fingerprint beyond its identifier | `C-RD/T133`: availability comparison only; no unpublished overlap or distinction inferred | `C-GRUN/T133`: availability comparison only | `C-DB/T133`: availability comparison only |

The refreshed supplied knowledge library has no `t132/` or `t133/` entry, no
matching report, and no source pin. The orchestration input contains each
identifier only in T134's mandatory comparison sentence. These rows therefore
record the exact inspectability boundary rather than invent active
fingerprints. They must be refreshed if readable artifacts appear before
adjudication.

## 8. Separately labeled unproved pi-transfer premise

**PI-ZERO-OCCUPANCY (`conjecture`; unproved and not asserted).** For every
integer `A>=1`, there exists an integer `m0>=1` such that for every integer
`m>=m0`, there exists an integer `N>=A*m` satisfying

```text
Z_m(pi,N)^2<=N^2/(6*A*m).                                  (8.1)
```

No source in this audit proves (8.1). C-RD fails to certify it by (4.6)--(4.7),
C-GRUN concerns another point and fails its own all-`A` occupancy test, and
C-DB constructs a different decimal. Equation (8.1) is only the exact missing
one-fiber premise requested by this audit.

Even conditionally on (8.1), no fixed-pi, C1, or C2 conclusion follows. The
positive-cylinder sum (2.7) remains independent and could be as large as
`(N-Z_m)^2`; controlling one fiber does not control total collision energy.
Replacing (8.1) by a total-energy assertion would merely restate T7 and is not
proposed.

## 9. Replay and endpoint

From a directory containing only the delivered artifacts, run

```text
python3 verify_t134.py
sha256sum -c SHA256SUMS
```

The verifier checks the canonical, T7, source, and comparator hashes; converts
the cited physical pages of all six PDFs with `pdftotext -layout` and checks
page-scoped theorem anchors; checks the source and candidate caps; replays
finite ordered zero-pair identities and representative exact instances of the
displayed threshold substitutions; and checks the presence of every comparison
cell, the T132/T133 availability boundary, the separate premise, the unique
verdict, successor count, and scope firewalls. Direct inspection of the
symbolic substitutions and comparison content remains necessary. The replay
is an experiment and transcription test only.

SCOPED_VERDICT (1/1): **close**. This closes only the audited claim that known
restricted-approximation, G-value maximum-run, or symbolic exact-incidence
theorems provide a new single-cylinder heavy-fiber mechanism for the
prescribed decimal orbit. C-RD and C-GRUN fail the explicit occupancy screen;
C-DB passes for a constructed model but is exactly the prior global-incidence
fingerprint. The zero fiber remains the exact T130 degeneracy, and its separate
control would still leave every positive cylinder uncontrolled. No bounded
successor is proposed.
