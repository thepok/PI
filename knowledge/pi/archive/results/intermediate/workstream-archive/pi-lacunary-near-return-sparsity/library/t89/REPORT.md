# T89: adjacent exact-arithmetic obstruction models

Search date: 2026-08-09 UTC.

Claim status: `literature-checked` for the three statements pinned in
`SOURCE_PINS.md`; `machine-checked` only for the types quoted from the three
vendored Lean interfaces; `proof sketch` for the elementary derivations below;
and `experiment` for the bounded replay. This report proves no estimate,
normality statement, C1, C2, or digit assertion for pi.

`PRIMARY_SOURCE_COUNT: 3`

`RETAINED_CANDIDATE_COUNT: 2`

`FINAL_VERDICT_COUNT: 2`

## 1. Immutable statement and quantifiers

The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

For integers `n,N>=1`,

\[
 Q_\pi(n,N)=\#\{(i,j):0\le i,j<N,
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}.
\tag{1.1}
\]

Pairs are ordered, all `N` diagonal pairs are included, and the cutoff is
strict. The open statement is exactly

\[
 \forall A\ge1\ \exists n_0\ge1\ \forall n\ge n_0\ \exists N\ge1:
 \quad AnQ_\pi(n,N)\le N^2.                              \tag{1.2}
\]

`N` may depend on `A,n`. This report does not substitute infinitely many
depths, one fixed `A`, prescribed `N`, off-diagonal or unordered pairs,
non-strict distance, another base, or bounded evidence. Both constants below
are explicit sibling objects under ambiguity A13/A14, never replacements for
pi.

For either retained real sibling `x`, notation below means exactly

\[
 Q_x(n,N)=\#\{(i,j):0\le i,j<N,
 \|(10^i-10^j)x\|_{\mathbb R/\mathbb Z}<10^{-n}\},
 \qquad n,N\ge1.                                          \tag{1.3}
\]

Thus all sibling collision claims retain ordered pairs, the diagonal, and the
strict cutoff.

## 2. Search protocol and exclusions

The dated search used Crossref title and DOI queries, DOI landing records,
primary PDFs, and the supplied accepted local library. It screened sparse
power-series constants, automatic/Mahler constants, Stoneham constants,
continued-fraction constants, and constructed normal numbers. It is bounded,
not exhaustive.

Exactly two constants and three primary sources are retained. This is below
the caps of four candidates and eight sources. A fourth candidate was not
added merely to fill the cap.

### 2.1 Required exclusions

| screened family | normalized fingerprint | reason not retained |
|---|---|---|
| Stoneham constants | constructed sparse series with pure-power modular orbit and sourced normality/exponential sums | literal duplicate: the literature-checked T63 audit already records the encompassing Bailey--Crandall constructed constants at `prior-t63-REPORT.md` lines 260--297 |
| Champernowne and concatenation constants | normality or explicit digits without adaptive fixed-pi phase control | excluded by the agenda and canonical A14; no normality-only transfer is admitted |
| new pi series, factorial, Machin, Ramanujan, Chudnovsky, or scalar irrationality approximants | rational transfer, valuation/order, finite certification, or scalar packing | expressly outside T89 after T63, T68, T78--T82, T85--T87 |

Stoneham arithmetic is mathematically cleaner than the pi approximants, but
retaining it would duplicate T63's exact constructed-constant source lane.

### 2.2 Non-duplication table for retained candidates

Rows marked `proof sketch` are comparison memory only, not premises.

| prior item and level | recorded boundary | Kempner/Fredholm comparison | decimal Thue--Morse comparison |
|---|---|---|---|
| T63, `literature-checked` applicability audit | rational phases and constructed normal constants do not supply adaptive fixed-pi cancellation | no odd/coprime modulus survives at all; the post-transient phase is exactly resonant | pure powers of 10 also leave no coprime tail; the new input is infinite substitution structure, not a pi representation |
| T68, `machine-checked`, route-specific | corrected-Zudilin transient and accuracy ranges are incompatible | accuracy leaves a long post-transient window, but that window collapses to zero | transient consumes every nonzero point of each decimal truncation |
| T78, `proof sketch`, sources pinned | exact factorial order/occupancy plus fast truncation still has fatal scale | opposite endpoint `m=1`: small modulus is no help without a nontrivial orbit | `m=1`, but the infinite word gives an independent exact symbolic collision lower bound |
| T79/T85, `proof sketch`, sources pinned | prime-power factors, ties, residues, and special numerators need audit | no valuation tie: numerator is `1 mod 10`; failure is complete noninvertibility | at most two terminal zeroes are explicit; failure is again complete noninvertibility |
| T80, `proof sketch` | ideal order need not be a real-character period | rational, so no ideal mismatch; there is simply no unit-group orbit | symbolic shift recursion is not asserted to be a circle-character period |
| T81, `proof sketch` with checked inputs | scalar irrationality does not provide adjacent compatibility | Kempner transcendence is unused in the collision derivation | Badziahin--Zorin approximation is unused in the collision derivation |
| T82, `proof sketch` with checked T64 input | finite carry certification does not give coherent Fourier/boundary control | exact sparse digits give the wrong, clustered behavior | carry-free digits `0/1` still give the wrong, linearly complex behavior |
| T86, `literature-checked` audit, `prior-t86-REPORT.md` lines 570--604 | semigroup density and scalar approximants miss diagonal adaptive sums | complete orbit information is available but maximally resonant | complete symbolic recurrence is available but collision-rich |
| T87 survey note, mixed and unverified, `prior-t87-REPORT.md` lines 469--484 | exact rational order, regrouping, and artificial streams do not themselves transfer | retained only as a negative model isolating the missing conductor | retained only as a negative model isolating the missing phase-coding inequality |

Thus the names are new to the inventory, but neither is presented as a new
fixed-pi route. Their non-duplicative value is a pair of exact endpoint models:
an accurate sparse truncation with modulus `1`, and an infinite automatic word
whose linear language forces too many collisions.

## 3. Named accepted interfaces

The following are byte-vendored, machine-checked interfaces. Their conditional
premises are not claims about pi.

1. **T7 finite cylinder energy.** Lines 292--318 of
   `T7FiniteCylinderEnergy.lean` give
   \[
     E_\pi(n,N)\le Q_\pi(n,N)\le3E_\pi(n,N).              \tag{3.1}
   \]
   Lines 346--386 retain exactly the quantifiers in (1.2).
2. **T10 long-lag resonance.** Lines 829--894 of
   `T10LongLagResonance.lean` say that failure of (1.2) supplies one `A`,
   arbitrarily large `n`, and for every `K>=1` integers
   \[
     N=16AnK,\quad 1\le r<N,\quad J=N-r\ge K,
     \quad1\le h\le256An                                  \tag{3.2}
   \]
   with
   \[
    \left|\sum_{j=0}^{J-1}e(h(10^r-1)10^j\pi)\right|
      >{J\over131072A^2n^2}.                               \tag{3.3}
   \]
3. **T61 direct-label variance.** Lines 293--338 of
   `T61DirectLabelAdjacentPhaseVariance.lean` give the exact identity
   `correlation.re = mass - variance/2`. Lines 340--418 require the strict
   complete variance bound, including predecessor, endpoint, and Fejer
   budgets. A symbolic recurrence alone does not satisfy that premise.

## 4. Candidate 1: Kempner/Fredholm sparse-power constant

### 4.1 Source and exact representation

**SOURCE THEOREM.** Kempner, printed p. 477, gives transcendence for the
displayed family

\[
 \sum_{m\ge0}{\alpha_m\over a^{2^m}}(p/q)^m
\tag{4.1}
\]

under its stated bounded-integral-coefficient conditions. Printed p. 482
explicitly specializes `p/q=1` and mentions Fredholm's function
`sum x^(2^m)`. Taking `a=10` and every `alpha_m=1` gives the transcendental
constant

\[
 \kappa=\sum_{m\ge0}10^{-2^m}
       =0.1101000100000001\ldots .                         \tag{4.2}
\]

Transcendence is source context only. None of the arithmetic consequences
below uses it except to note that actual orbit points cannot coincide exactly.

The exact functional recurrence, derived by splitting off `m=0`, is

\[
 F(z)=\sum_{m\ge0}z^{2^m}=z+F(z^2),\qquad \kappa=F(1/10).
\tag{4.3}
\]

### 4.2 Denominator, modulus, transient, and order

For `M>=0`, let `t_M=2^M` and truncate inclusively:

\[
 \kappa_M=\sum_{m=0}^M10^{-2^m}={A_M\over10^{t_M}},\qquad
 A_M=\sum_{m=0}^M10^{t_M-2^m}.                            \tag{4.4}
\]

**DERIVATION.** The last summand in `A_M` is `1`; all earlier summands are
divisible by 10. Hence

\[
 A_M\equiv1\pmod {10},\qquad
 \boxed{q_M=10^{2^M}\text{ is the reduced denominator}.} \tag{4.5}
\]

For `0<=j<t_M`, cancellation of exactly `10^j` leaves reduced denominator
`10^(t_M-j)`. For every `j>=t_M`, `10^j kappa_M` is integral. Therefore

| decimal arithmetic | exact value |
|---|---|
| reduced denominator | `q_M=10^(2^M)` |
| 2/5 transient | `t_M=2^M` |
| coprime post-transient modulus | `m_M=1` |
| eventual orbit | fixed point `0` |
| eventual period | `1` |
| multiplicative order | unavailable for `q_M`; conventionally `ord_1(10)=1` after removing 2/5-parts |
| distinct rational orbit points | `t_M+1`, including the final zero |

There is no nontrivial conductor or multiplicative subgroup.

### 4.3 Truncation range and actual orbit

Put `R_M=kappa-kappa_M` and `q=q_M`. Since

\[
 R_M=q^{-2}+q^{-4}+q^{-8}+\cdots,
\]

comparison with the ordinary geometric series gives

\[
 \boxed{q^{-2}<R_M<{q^{-2}\over1-q^{-2}}}.                \tag{4.6}
\]

The decimal orbit has the exact tail formula

\[
 x_j=\{10^j\kappa\}
    =\sum_{2^m>j}10^{-(2^m-j)}.                           \tag{4.7}
\]

At `t=2^M` and `0<=s<t`,

\[
 x_{t+s}=10^{-(t-s)}+10^{-(3t-s)}+10^{-(7t-s)}+\cdots .  \tag{4.8}
\]

Consequently, if `0<=s<=t-n-1`, then `0<x_(t+s)<10^(-n)`.
The accurate post-transient window is not random: it is a near-zero cluster.

### 4.4 Collision and exponential-sum consequences

Let `w_r=1` exactly when `r` is a positive power of two. A length-`n` block
starting at `j` is `(w_(j+1),...,w_(j+n))`. If `j>=n`, the interval
`(j,j+n]` contains at most one power of two, because the gap between two
successive powers is the smaller power, greater than `j>=n`. Thus starts
`j>=n` produce at most `n+1` blocks (one all-zero block and one for each
possible location of a `1`); the first `n` starts add at most `n` more.
Therefore the factor complexity satisfies

\[
 \boxed{p_\kappa(n)\le2n+1}.                              \tag{4.9}
\]

For `N` starts, let `c_w` be the multiplicity of block `w`. Equal blocks are
in one decimal cylinder, so their orbit distance is strictly below `10^-n`.
Cauchy--Schwarz gives the ordered, diagonal-inclusive sibling count

\[
 Q_\kappa(n,N)\ge\sum_wc_w^2\ge{N^2\over p_\kappa(n)}
 \ge {N^2\over2n+1}.                                     \tag{4.10}
\]

For `A=3`, every `n>=2`, and every `N>=1`, `3n/(2n+1)>1`; hence

\[
 3nQ_\kappa(n,N)>N^2\quad\text{for every }N.              \tag{4.11}
\]

This proves failure of the exact **kappa sibling**, not any statement about
pi.

The same clustering gives a signed consequence. For integer `c` and
`L<=t-n`, (4.8) and `|e(y)-1|<=2*pi*|y|` imply

\[
 \left|\sum_{s=0}^{L-1}e(c10^{t+s}\kappa)\right|
 \ge L(1-2\pi|c|10^{-n}).                                \tag{4.12}
\]

For the rational truncation, every post-transient term is exactly `1`, so the
sum is exactly `L`. Accurate pure-base truncation here produces resonance,
not cancellation.

### 4.5 Explicit transfer hypothesis and kill test

The nearest named pi interface is T10. Let `u/q` be a reduced rational
approximant, put `c=h(10^r-1)>0`, and factor

\[
 q=2^a5^b m,\quad(m,10)=1,\quad t=\max(a,b)<J.            \tag{K1}
\]

Define the post-transient numerator modulo `m` by

\[
 u_t\equiv u2^{t-a}5^{t-b}\pmod m,
\tag{K1a}
\]

with `u_t=0` when `m=1`. The exact identity is

\[
 e(c10^{t+s}u/q)=e(cu_t10^s/m).                           \tag{K1b}
\]

A rational-tail use of this mechanism would need (K1), uniformly for every
legal adaptive tuple (3.2), together with the explicit half-threshold
approximation condition

\[
 \left|\pi-{u\over q}\right|
 \le {9J\over524288\pi A^2n^2c(10^J-1)},                 \tag{K1c}
\]

and the rational-phase cancellation certificate

\[
 t+\left|\sum_{s=0}^{J-t-1}e(cu_t10^s/m)\right|
 \le {J\over262144A^2n^2},\qquad c=h(10^r-1).             \tag{K2}
\]

Indeed, `|e(x)-e(y)|<=2*pi*|x-y|` and geometric summation make (K1c) bound
the pi-to-rational sum error by `J/(262144 A^2 n^2)`. Splitting the rational
sum at `t`, bounding its first `t` terms trivially, and using (K1b)--(K2) gives
the same bound for the rational sum. Their sum contradicts (3.3). Thus
(K1)--(K2) are a fully quantified sufficient transfer package, not a theorem
about pi. They name the nontrivial coprime conductor and special-numerator
cancellation absent from the model.

**Smallest kill test.** Already `M=0` has `q=10`, `t=1`, and `m=1`. For every
`J>1`, the post-transient sum in (K2) has magnitude `J-1`, so the left side is
exactly `J`, while the right side is at most `J/262144`. Thus (K2) fails at the
first truncation. This kills the proposed truncation/conductor application,
not every conceivable theorem about the infinite constant.

## 5. Candidate 2: decimal Thue--Morse constant

### 5.1 Source, recurrence, and exact representation

**SOURCE FORMULAS.** Badziahin--Zorin, PDF pp. 3--4, equations (3)--(5),
define

\[
 t_0=0,\qquad t_{2m}=t_m,\qquad t_{2m+1}=1-t_m,           \tag{5.1}
\]

and, with `epsilon_m=(-1)^(t_m)`,

\[
 f_{TM}(z)=\sum_{m\ge0}\epsilon_mz^{-m}
 =\prod_{k\ge0}(1-z^{-2^k}),\qquad
 f_{TM}(z^2)={z\over z-1}f_{TM}(z).                      \tag{5.2}
\]

The source's named constant uses base 2. The retained decimal sibling is
explicitly

\[
 \tau_{10}=\sum_{m\ge0}t_m10^{-(m+1)}
 =0.0110100110010110\ldots .                              \tag{5.3}
\]

**DERIVATION.** Since `t_m=(1-epsilon_m)/2`, geometric summation gives

\[
 \boxed{\tau_{10}={1\over18}-{1\over20}f_{TM}(10)}.       \tag{5.4}
\]

The exact decimal orbit is the symbolic shift:

\[
 y_j=\{10^j\tau_{10}\}
 =\sum_{r\ge0}t_{j+r}10^{-(r+1)},\qquad
 y_{j+1}=10y_j-t_j.                                      \tag{5.5}
\]

Badziahin--Zorin Theorem 2 supplies a scalar restricted-approximation result
for the product family at integer arguments. It is not used below: scalar
approximation does not provide T61's phase variance.

### 5.2 Decimal denominator, transient, and truncation range

For `K>=2`, let

\[
 A_K=\sum_{m=0}^{K-1}t_m10^{K-1-m},\qquad
 \tau_{10}^{(K)}={A_K\over10^K}.                          \tag{5.6}
\]

Let `z_K` be the number of terminal zeroes in the word
`t_0...t_(K-1)`. Every pair `(t_(2m),t_(2m+1))` is mixed, so three consecutive
zeroes cannot occur. Hence `z_K` is `0`, `1`, or `2`. Removing those terminal
zeroes leaves a numerator ending in `1`, and therefore

\[
 \boxed{q_K=10^{K-z_K}}                                  \tag{5.7}
\]

is the reduced denominator.

| decimal arithmetic | exact value |
|---|---|
| reduced denominator | `10^(K-z_K)`, `z_K in {0,1,2}` |
| 2/5 transient | `K-z_K` |
| coprime post-transient modulus | `1` |
| eventual orbit | fixed point `0` |
| eventual period | `1` |
| multiplicative order | unavailable before the transient; `ord_1(10)=1` by convention afterward |
| distinct rational orbit points | `K-z_K+1` |

Every three consecutive Thue--Morse digits contain a `1`. The first omitted
`1` is therefore no later than the third omitted position, while replacing
all omitted digits by `1` gives the upper bound

\[
 \boxed{10^{-(K+3)}\le\tau_{10}-\tau_{10}^{(K)}
       \le {10^{-K}\over9}.}                              \tag{5.8}
\]

In terms of `q_K`, these truncations have error `Theta(1/q_K)`, not the
quadratic scale of (4.6). Their transient consumes the complete rational
orbit.

### 5.3 Exact factor complexity and collision consequence

**SOURCE FORMULA.** Hwang--Janson--Tsai, PDF pp. 15--16, Example 3.2,
equation (3.4), and Table 3 give the exact divide-and-conquer solution and
identify `A005942(n+1)=2(f(n)+2)` as Thue--Morse factor complexity. Substitution
gives, for `n>2` and `r=n-1`,

\[
 \boxed{p_{TM}(n)=3r+\min_{a\ge0}|r-2^a|}.                \tag{5.9}
\]

Equivalently, for `m>=2`,

\[
 p_{TM}(2m)=p_{TM}(m)+p_{TM}(m+1),\qquad
 p_{TM}(2m+1)=2p_{TM}(m+1),                              \tag{5.10}
\]

with `p_TM(1)=2`, `p_TM(2)=4`, `p_TM(3)=6`.

The distance from positive `r` to the nearest power of two is at most `r/3`
(the worst ratio occurs halfway in the multiplicative interval). Thus

\[
 3(n-1)\le p_{TM}(n)\le {10\over3}(n-1)\quad(n>2).        \tag{5.11}
\]

For `N` starts, equal length-`n` factors lie in one decimal cylinder. The
digits are only `0,1`, so the distance is strictly below `10^-n`. As in (4.10),

\[
 Q_{\tau_{10}}(n,N)\ge {N^2\over p_{TM}(n)}.              \tag{5.12}
\]

For every `n>=3` and every `N>=1`,

\[
 4nQ_{\tau_{10}}(n,N)
 \ge {4nN^2\over p_{TM}(n)}
 \ge {6n\over5(n-1)}N^2>N^2.                             \tag{5.13}
\]

Thus the exact **tau_10 sibling** fails the canonical inequality at `A=4`.
This is a collision-rich automatic model, not information about pi.

### 5.4 Explicit transfer hypothesis and kill test

The nearest named phase interface is T61. Use the exact T61 notation in the
vendored file: `terminalShell R`, `triangularWeight R u`,
`directFrequency ell u j`, `precedingCharacter`, `incomingShift`,
`directTerminalMass`, `predecessorRemainderBudget`, and `endpointBudget`.
For every required legal tuple `(chain,k,ell,R,delta)`, a Thue--Morse transfer
would additionally need a map

\[
 s:\operatorname{terminalShell}(R)\times\operatorname{range}(\ell)
   \longrightarrow\mathbb N                                  \tag{TM0}
\]

and one fixed `epsilon>0` such that, for every actual label `(u,j)`,

\[
 \begin{aligned}
 &\operatorname{precedingCharacter}(\beta,
   10^{\operatorname{incomingShift}}\operatorname{directFrequency}(\ell,u,j))
     =(-1)^{t_{s(u,j)+1}},\\
 &\operatorname{precedingCharacter}(\beta,
   \operatorname{directFrequency}(\ell,u,j))
     =(-1)^{t_{s(u,j)}},
 \end{aligned}                                             \tag{TM1}
\]

where `beta=chain.nodeCoefficient k`, and

\[
 \sum_{u,j}\operatorname{triangularWeight}(R,u)
   |(-1)^{t_{s(u,j)+1}}-(-1)^{t_{s(u,j)}}|^2
 \le(2-\epsilon)\operatorname{directTerminalMass}(\ell,R), \tag{TM2}
\]

together with the exact remaining budget

\[
 2\operatorname{predecessorRemainderBudget}
 +2\operatorname{endpointBudget}
 +{\ell\over4R\delta^2}
 <\ell+\epsilon\operatorname{directTerminalMass}(\ell,R). \tag{TM3}
\]

By (TM1), the left side of (TM2) is exactly T61's
`directAdjacentVariance`. Combining (TM2)--(TM3) gives the strict predicate at
vendored lines 344--353. This is a literal sufficient transfer package;
neither source states (TM0)--(TM3).

**Smallest kill test.** A proposed transfer is killed by one actual label for
which either equality in (TM1) fails. If every label passes, compute the two
finite sides of (TM2) and then (TM3); failure of either inequality kills it.
For the most literal unweighted adjacent-sign proposal, the first three edges
already give signs `(1,-1,-1,1)` and squared variation `4+0+4=8>2*3=6`, so
that proposal fails (TM2) before the remaining budgets. At the theorem level,
the current source application is killed even earlier: the pinned source
statements contain no map depending on `beta`, `directFrequency`, `u`, and
`j`, so they do not supply (TM1).

## 6. Arithmetic comparison

| quantity | Kempner/Fredholm | decimal Thue--Morse |
|---|---|---|
| exact representation | `sum 10^(-2^m)`; `F(z)=z+F(z^2)` | substitution (5.1), product (5.2), affine value (5.4) |
| reduced truncation denominator | `10^(2^M)` | `10^(K-z_K)`, `z_K<=2` |
| transient | `2^M` | `K-z_K` |
| coprime modulus | `1` | `1` |
| eventual orbit/order | zero fixed point / period 1 | zero fixed point / period 1 |
| error scale | strictly between `q^-2` and `q^-2/(1-q^-2)` | between `10^(-K-3)` and `10^(-K)/9` |
| usable infinite structure | long near-zero clusters | exact shift substitution |
| rigorous consequence | `p(n)<=2n+1`, hence `Q>=N^2/(2n+1)`; near-maximal sums | exact linear `p_TM(n)`, hence `Q>=N^2/p_TM(n)` |
| named frontier | T10 | T61, with T7 as the collision comparison |
| first missing input | nontrivial conductor plus special-numerator cancellation | exact actual-label phase coding plus strict complete variance budget |
| smallest kill | `M=0` gives `m=1` and K2-left-side `J` | one failed TM1 label; literal first-three-edge proposal also gives `V=8>6` |

The arithmetic comparison is deliberately normalized: both truncation
families are pure powers of ten, yet their infinite objects fail for different
structural reasons. Kempner's very accurate truncations create long resonance;
Thue--Morse's exact recurrence creates only linearly many blocks. Neither
mechanism supplies an upper collision estimate or adaptive cancellation.

## 7. Replay and non-claims

From a directory containing only the delivered artifacts, run

```text
python3 verify_note.py
sha256sum -c SHA256SUMS
```

The replay checks all source/local hashes and PDF anchors, both caps, exact
truncation arithmetic at bounded scales, denominator reduction, transients,
factor-complexity formulas, collision ratios, and both kill tests. Those
finite checks are `experiment` transcription tests, never proof of the
universal derivations and never evidence about pi.

No formula here identifies either model with pi. No source or derivation gives
the transfer hypotheses (K1)--(K2) or (TM1)--(TM2) for pi. The two sibling
failures do not imply failure of (1.2), and their exact digits do not imply any
digit statement about pi.

FINAL VERDICT C1: hold as model

FINAL VERDICT C2: hold as model
