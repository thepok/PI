# T115: base-ten substitution Riesz recursion scout

Search date: 2026-08-10 UTC.

Claim labels: statements attributed to the four pinned papers are
`literature-checked`.  The specialisation to `(k,l)=(5,5)`, the coefficient
recurrences, decimal-ray substitutions, and T67 calculations below are
`proof sketch` deductions written out in full.  The replay is an `experiment`
that checks transcription and exact finite arithmetic; it is not evidence for
an asymptotic theorem or for pi.

```text
PRIMARY_SOURCE_COUNT: 4
PRIMARY_SOURCE_CAP: 10
CANDIDATE_COUNT: 1
CANDIDATE_CAP: 3
TERMINAL_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
```

## 1. Immutable statement and normalized scope

The delivered `canonical_statement.txt` is a byte-exact copy of
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.  Its SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

For integers `n,N>=1`, the canonical count is

```text
Q_pi(n,N) = #{(i,j) in {0,...,N-1}^2:
               ||(10^i-10^j)pi||_(R/Z) < 10^(-n)}.
```

Pairs are ordered, the diagonal is included, and the inequality is strict.  The
open quantifiers are

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N>=1 with
A*n*Q_pi(n,N) <= N^2.
```

T115 changes the point and statistic.  It studies finite Riesz approximants and
diffraction coefficients of named substitution systems.  These are A13/A14
siblings only.  Nothing below asserts a bound for `Q_pi`, C1, C2, normality,
decimal factor complexity, or digit occurrence for pi.

The potentially ambiguous agenda phrases are fixed as follows.

1. A source is counted once although its PDF and `pdftotext -layout` derivative
   are both delivered.
2. A candidate is retained only if a named system has an exact finite-scale
   coefficient recursion and the substitution `m=h*10^r` is displayed.
3. A decimal ray means integer frequencies `{h*10^r:r>=0}` with fixed nonzero
   integer `h`; it is not a limit over an ambient measure.
4. A finite Riesz approximant is treated as a finite probability density.  The
   limiting invariant measure is not used as an invariant-measure separator or
   transferred through a generic point.
5. T67 comparison means its literal terminal shell and triangular weight.  No
   abstract cutoff array is claimed to be a pi empirical Fourier array.
6. Active T113 and T114 had leases but no readable result artifact in this
   sandbox snapshot.  No fingerprint is inferred from their task numbers.

## 2. Bounded clean-context search

Four primary papers were opened and the search stopped.  They cover the three
requested lanes without filling either cap:

| ID | Lane | Paper | Role |
|---|---|---|---|
| S1 | substitution collision/diffraction and fractal Riesz analysis | Baake--Gahler--Grimm, generalized Thue--Morse family | sole retained candidate |
| S2 | fixed-point lacunary spectral cocycles | Marshall-Maldonado, bijective substitutions | screened modern comparator |
| S3 | explicit fixed-point diffraction | Baake--Grimm, period doubling | screened prior-overlap comparator |
| S4 | symbolic singular-continuous Riesz products | Baake--Grimm, classical Thue--Morse | screened wrong-radix comparator |

`SOURCE_PINS.md` gives URLs, DOIs, hashes, and exact locators.
`SEARCH_LOG.md` records the bounded queries and exclusions.

S2 is the preferred-date source (2024).  S1, S3, and S4 are retained as
indispensable older sources because they print the exact coefficient and Riesz
recursions rather than only asymptotic spectral language.

## 3. Sole candidate: the base-ten generalized Thue--Morse system

### 3.1 Source-pinned definition and exact recursion

S1 Eq. (11), printed p. 8, defines for positive integers `k,l`

```text
rho_(k,l):  1 -> 1^k (-1)^l,       -1 -> (-1)^k 1^l.       (3.1)
```

Retain exactly the named specialisation `rho_(5,5)`, a constant-length ten
primitive substitution.  S1 Lemma 1, printed pp. 9--11, states for every
integer `m` and every integer `s` with `0<=s<k+l` that its autocorrelation
coefficients satisfy

```text
eta((k+l)m+s)
 = [alpha_s eta(m)+alpha_(k+l-s) eta(m+1)]/(k+l),          (3.2)

alpha_s = k+l-s-2*min(k,l,s,k+l-s),       eta(0)=1.
```

In particular, `eta((k+l)m)=eta(m)`.  At `(k,l)=(5,5)`, S1's formula before
Eq. (13), printed p. 9, also gives

```text
eta(1)=(k+l-3)/(k+l+1)=7/11.                              (3.3)
```

Thus the limiting coefficients have `eta(h*10^r)=eta(h)`, and in particular
`eta(10^r)=7/11`.  This limiting observation is only a consistency check.  The
retained mechanism is the finite recursion below, not invariance of the limit.

### 3.2 Exact finite Riesz recursion

S1 Proposition 3 and Eqs. (22)--(23), printed pp. 16--18, define

```text
theta(x)=1+(2/10) sum_(s=1)^9 alpha_s cos(2*pi*s*x),
f_0(x)=1,
f_(N+1)(x)=theta(x) f_N(10x),
f_N(x)=product_(j=0)^(N-1) theta(10^j*x).                 (3.4)
```

The source proves `theta>=0`, integral `theta=1`, and identifies the vague
limit as the generalized Thue--Morse Riesz product.  For the finite probability
density define

```text
c_N(m)=integral_0^1 exp(2*pi*i*m*x) f_N(x) dx.             (3.5)
```

Since the Fourier support of `theta` is `{-9,...,9}` and

```text
theta_hat(0)=1,
theta_hat(+-s)=alpha_s/10       (1<=s<=9),                 (3.6)
```

Fourier multiplication in (3.4) gives, for every `N>=0` and integer `m`,

```text
c_(N+1)(m)
 = sum_[a in {-9,...,9}, a congruent to m (mod 10)]
     theta_hat(a)c_N((m-a)/10).                            (3.7)
```

This is an exact finite-scale recursion.  It has at most two nonzero summands
for any fixed `m`; no exponentially large coefficient vector is needed to
evaluate one ray.

If `m=10q`, only `a=0` in the support satisfies the congruence, so

```text
c_(N+1)(10q)=c_N(q).                                      (3.8)
```

Iteration gives the requested decimal-ray substitution with all quantifiers:

```text
for every h in Z, r>=0, and N>=r,
c_N(h*10^r)=c_(N-r)(h).                                   (3.9)
```

At `(5,5)`, `alpha_1=7` and `alpha_9=-1`.  In (3.7) with
`m=1`, the only possibilities are `(a,b)=(1,0),(-9,1)`.  Since every `f_N`
has mass one,

```text
c_(N+1)(1)=7/10-(1/10)c_N(1),       c_0(1)=0.             (3.10)
```

Solving the affine recursion yields

```text
c_N(1)=(7/11)(1-(-1/10)^N),

c_N(10^r)=(7/11)(1-(-1/10)^(N-r))       (N>=r).           (3.11)
```

Consequently

```text
c_(r+1)(10^r)=7/10                                      (3.12)
```

for every `r>=0`, and more generally
`|c_N(10^r)|>=63/100` whenever `N>=r+1`.

### 3.3 Why S2 does not repair the quantifiers

S2 Lemma 2.16, printed p. 9 and explicitly credited there to BCM20 Remark 4.3,
restates an exact scalar product for the spectral cocycle of a length-`q`
binary substitution.  S2's own Theorem 3.5 and proof, printed p. 13, give
subexponential deviation for almost every fixed frequency
`omega`, with a threshold `n0(omega)`.  Substitution of
`omega=h*10^r*pi` merely changes the product to a shifted decimal orbit of
phases.  The theorem has no exceptional-set removal for pi, no uniformity over
the growing T64 box `0<|h|<=8000*10^(3ell)`, no one-prefix triangular
quantifier, and no T107 boundary estimate.  It is therefore screened rather
than used as a premise.

## 4. Literal quantitative T67 comparison

The controlling machine-checked file is
`knowledge_library/t67/TerminalRayStrength.lean`, SHA-256
`e9fc18166d2b31c52adbfe73bfcbb10ccd8d93c785fb39144b88db75ed493dff`.
Lines 138--160 define primitive bases and show that at `R=H+1` the terminal
shell is exactly

```text
Ioc(H/10,H)={u:H/10<u<=H}.                                 (4.1)
```

Lines 497--525 define the unweighted terminal mean square, the normalized
triangular mean square, and prove total triangular mass `H/2`.  The weight is
`w_(H+1)(u)=1-u/(H+1)`.

For every integer `r>=1`, choose

```text
H_r=2*10^r+1,       R_r=H_r+1,
u_r=10^r,           v=1,       N_r=r+1.                    (4.2)
```

Then `H_r/10=2*10^(r-1)<u_r<=H_r`, and
`u_r=10^r*v` with `10` not dividing `v`.  Thus `u_r` is on the literal
primitive decimal ray in the literal shell.  Equations (3.9)--(3.12) give

```text
|c_(N_r)(u_r)|=7/10.                                      (4.3)
```

The exact shell cardinality and weight are

```text
|Ioc(H_r/10,H_r)|=H_r-H_r/10=18*10^(r-1)+1,

w_(R_r)(u_r)=1-10^r/(2*10^r+2)
             =(10^r+2)/(2*10^r+2)>1/2.                   (4.4)
```

If the finite array `u -> c_(N_r)(u)` is inserted only into T67's two abstract
cutoff functionals, its named ray gives the checkable bounds

```text
shellSup >= 7/10,

terminalMeanSquare
 >= (49/100)/(18*10^(r-1)+1),

triangularMeanSquare
 >= [w_(R_r)(u_r)*(49/100)]/(H_r/2)
 > 49/[100*(2*10^r+1)].                                  (4.5)
```

The normalized bulk lower bounds in (4.5) tend to zero while the shell
supremum is constant.  This is a finite-scale, substitution-generated instance
of the sparse-ray obstruction.  It is not T67's abstract top-frequency spike,
not a pi empirical array, and not evidence that the other coefficients have
small bulk mean.

For comparison, T107's machine-checked row defect is a maximum of a boundary
component and a Fourier component.  The controlling T64 file is pinned in
`SOURCE_PINS.md`; its lines 617--649 prove the collected nonzero `L1` bound,
and lines 1715--1720 define the two-scale row remainder.  Put

```text
S_P(h)=sum_(j=0)^(P-1) exp(2*pi*i*h*10^j*pi).
```

With `q=10^ell`, the exact sufficient premise for Fourier budget
`0<theta<1` is

```text
|S_P(h)| <= epsilon_ell(theta)*P
for every integer h with 0<|h|<=8000*q^3,                  (4.6)
```

where

```text
epsilon_ell(theta)
 = sqrt(theta/(160*q*W_ell)),
W_ell=[2+log(800*q^2+1)]^2
      +(1/2)[2+log(40*q^2+1)]^2.                          (4.7)
```

Indeed T64's two collected `L1` bounds give normalized Fourier defect at most
`160*q*W_ell*epsilon^2`; comparison with `theta` gives (4.7).  Premise (4.6)
must hold at one common prefix, together with the separate boundary budget.
Neither (3.7) nor S2 controls this unweighted pi sum, and (4.3) shows why a
coefficientwise identification with this
candidate would be harmful rather than useful.

## 5. Explicit fixed-pi transfer premise and cheap rejection test

Write the literal T67 empirical coefficient as

```text
A_J(m,pi)=J^(-1) sum_(j=0)^(J-1) exp(2*pi*i*m*10^j*pi).
```

The additional premise needed to identify the candidate arrays with the fixed
pi arrays is the following, stated but not asserted.

**FP-T67 finite-prefix transfer premise (conjecture).**  There exist a strictly
increasing sequence of positive integers `J_r`, integers `M_r>=r+1`, and
nonnegative reals `eps_r -> 0` such that, for every sufficiently large `r`,

```text
sup_[u in Ioc(H_r/10,H_r)]
  |A_(J_r)(u,pi)-c_(M_r)(u)| <= eps_r,
H_r=2*10^r+1.                                             (5.1)
```

The sources do not state (5.1).  Weak convergence at fixed frequencies would
not imply it because the shell and frequency grow with `r`.

**CHEAP_REJECTION_TEST: nondecaying decimal ray.**  Before attempting any
transfer, evaluate the candidate at the single legal label `u_r=10^r`.
Equation (3.11) gives

```text
|c_(M_r)(u_r)|>=63/100       whenever M_r>=r+1.            (5.2)
```

Hence (5.1) would imply

```text
|A_(J_r)(10^r,pi)|>=63/100-eps_r,                          (5.3)
```

which transfers a nondecaying ray, not T67 terminal-ray cancellation.  This
rejects the sole candidate as a source of the desired decay at the first
frequency.  It does not refute (5.1), T67's conditional theorem, or any future
mechanism that adds genuinely new fixed-pi cancellation.

## 6. Mandatory exclusion and prior-fingerprint comparison

The following table is a scope firewall.  Sketch-level reports are comparison
history only and are not treated as discharged premises.

| Comparator | Verification level used | Normalized fingerprint | T115 separation |
|---|---|---|---|
| T88, report SHA `ca481e2...` | unverified `proof sketch` with pinned sources and checked imported interfaces | invariant Bernoulli measure, generic point, persistent Fourier ray | T115 does not choose an invariant measure or generic point; (3.7) and (3.12) hold for finite Riesz densities before taking a limit |
| T91, SHA `a684f159...` | unverified `proof sketch`; source statements pinned where stated | Thue--Morse and period-doubling aligned block collisions; paperfolding representatives | no aligned block sampling or collision recurrence; S3 is screened because its system already appears there |
| T94, SHA `f399dfac...` | unverified `proof sketch` plus experiment | paperfolding tensor/profile recurrence | excluded; no paperfolding word or carry/profile state occurs |
| T97, SHA `fb3c58a4...` | unverified `proof sketch` plus experiment | paperfolding diagonal collision formula | excluded; no diagonal factor-count recurrence occurs |
| T101, SHA `ddd24794...` | unverified `proof sketch` plus experiment | paperfolding successor-splitting obstruction | excluded; no successor-energy argument occurs |
| T103, SHA `ed690a31...` | source statements literature-checked; deductions `proof sketch` | positive-entropy Toeplitz towers with persistent holes | excluded; no Toeplitz tower or hole density occurs |
| T104, SHA `2dee0c91...` | source statements literature-checked; transfers `proof sketch` | ambient fractal Fourier decay, fixed-fiber and Mahler comparators | T115 uses an exact finite coefficient identity, not decay for an ambient measure or almost every point |
| T110, SHA `4eaa088e...` | source statements literature-checked; transfers `proof sketch` | Gowers, nilsequence, and fixed-degree polynomial uniformity | excluded; sharing Thue--Morse ancestry does not make the Riesz coefficient recursion a Gowers argument |
| T112, SHA `72884fc7...` | source statements literature-checked; transfers `proof sketch` | finite carry cocycles and growing-state operators | excluded; (3.7) is a scalar Fourier recursion with no digit-carry state |
| active T113 | no readable artifact in this snapshot | unavailable | no content inferred and no dependence |
| active T114 | no readable artifact in this snapshot | unavailable | no content inferred and no dependence |
| terminal memory, SHA `aa8b0f84...` | unverified obstruction ledger | regrouping/model behavior is not fixed-pi cancellation; growing frequencies require prefix uniformity | obeyed: (5.1) is explicit and unproved, and the model obstruction is not promoted to a pi claim |

Full local hashes used above are recorded in `SOURCE_PINS.md`.  S3 period
doubling is screened because its pure-point decimal-ray recurrence is both a
less faithful spectral model and overlaps T91's named system.  S4 classical
Thue--Morse is screened because its radix-two recursion leaves the moving
residual index `h*5^r`, while T110 already covers its distinct higher-order
fingerprint.  S2's almost-everywhere cocycle estimate fails named-point and
prefix-uniform quantifiers.  Thus there is exactly one retained candidate.

## 7. Replay and scope firewall

From a directory containing only the delivered files, run

```text
python3 verify_t115.py
sha256sum -c SHA256SUMS
```

The verifier checks the canonical and source hashes, source anchors, hard caps,
the exact finite coefficient recursion, decimal-ray substitution, affine closed
form, T67 shell arithmetic, screened period-doubling recurrence, required prior
names, exclusion labels, and endpoint counts.  Its bounded checks are an
`experiment`; Sections 3--5 contain the universal `proof sketch` deductions.

No source states a theorem about pi.  No finite check proves a universal source
claim.  The fixed-pi premise (5.1) is not known.  Related-system diffraction is
not a claim about `Q_pi`, C1, or C2.

VERDICT: close

The bounded fingerprint is exhausted by the exact finite spike (3.12): radix
alignment creates persistent decimal-ray mass rather than anti-concentration.
No successor is selected.
