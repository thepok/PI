# T87: cross-program fixed-pi mechanism decision

Date of search: 2026-08-09 UTC.

Claim status: `literature-checked` for the four primary-source statements in
`SOURCE_PINS.md`; `machine-checked` only for theorem types quoted from the
vendored Lean inputs; `proof sketch` for the localized Bugeaud--Kim replay and
the two cross-program substitutions below; `experiment` only for the bounded
generic-word enumeration in `verify_note.py`. This report proves no fixed-pi
estimate, C1, C2, G11, G19, normality, or digit assertion.

`PRIMARY_SOURCE_COUNT: 4`

`CANDIDATE_COUNT: 3`

`TERMINAL_DECISION_COUNT: 1`

## 1. Immutable statement and quantifiers

The delivered `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

and is a byte-exact copy of the canonical source. For integers `n,N>=1`,

\[
 Q_\pi(n,N)=\#\{(i,j):0\le i,j<N,
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}.
\tag{1.1}
\]

Pairs are ordered, all `N` diagonal pairs are included, and the cutoff is
strict. The open statement is exactly

\[
 \forall A\in\mathbb N_{\ge1}\ \exists n_0\ge1\ \forall n\ge n_0\
 \exists N\ge1:\quad AnQ_\pi(n,N)\le N^2.                 \tag{1.2}
\]

`N` may depend on `A,n`. No infinitely-many-`n`, one-`A`, prescribed-`N`,
off-diagonal, unordered, exact-word, other-base, or almost-everywhere sibling
is substituted.

## 2. Required accepted inputs and dispositions

The exact hashes and line locators are in `SOURCE_PINS.md`. Verification
levels are part of every use.

1. **Positive-decimal-factor-entropy program.**
   `PFE_T86GroupedSquareBound.lean` is a promoted, axiom-audited
   `machine-checked` artifact. It proves the deterministic coefficient bound
   `D_N<42` for every `mu,c,Q0,N` with `1<=N`. Its header and final theorem
   expressly prove no estimate at `Real.pi`, C7, C2, C1, or entropy.
   `PFE_T61VaalerAnalytic.lean` exposes the load-bearing conditional chain:
   `EffectiveIrrationality`, `SparseLongResidualLinearBound`, and
   `SignedStructuredDenominatorPremise` imply the positive-entropy program's
   C7, then its C2 and C1. The last premise has quantifiers
   `exists B>0, exists N>=1, forall n>=N` and bounds the complete signed
   Vaaler expression by `B*L_n`.
2. **Long-lag-block-collision program.**
   `LL_T87RecordDiagonalCriticalBand.lean` is a promoted, axiom-audited
   `machine-checked` artifact. In the critical band
   `10^m<=N^2<=2*10^m`, it computes and bounds the record diagonal, including
   both orientations and frequencies `1<=h<=10^m`. Its header expressly
   leaves the centered off-diagonal term and all C1/C2/C3 conclusions open.
3. **Lacunary-near-return program.**
   `NRS_T86_REPORT.md` is the accepted `literature-checked` bounded audit.
   The skeptic disposition in `WORKFLOW_CONTEXT.json` says its source hashes,
   theorem anchors, transfer constants, and unique negative endpoint replayed
   successfully. It retains no surviving candidate and makes no fixed-pi
   claim.
4. **Two external reviews.** The raw feedback is explicitly `conjecture and
   audit input only`; its hash is recorded in the vendored T83 disposition.
   `T83_REVIEW_DISPOSITION.md` reports that Review A's constant-stream
   existential mechanism is machine-checked, while Review B's universal
   `3/2` charging claim remains an underspecified `conjecture`. The T83 skeptic
   disposition in `WORKFLOW_CONTEXT.json` accepts exactly that scoped result,
   not Review B itself.
5. **Semantic obstruction memory.** `SEMANTIC_OBSTRUCTION_MEMORY.md` records,
   with verification levels, that scalar irrationality, exact regrouping,
   isolated rows, rational order, and finite certification do not by
   themselves supply adaptive fixed-pi cancellation. These are comparison
   warnings, not mathematical premises.

The unverified T78, T79, T80, T81, T82, and T85 notes are used only to name
candidate formulas or compare fingerprints. Any arithmetic conclusion that
depends on those notes is explicitly conditional on their formulas.

## 3. Common accepted frontiers

The lacunary T7 finite-cylinder interface gives

\[
 E_\pi(n,N)\le Q_\pi(n,N)\le3E_\pi(n,N).                 \tag{3.1}
\]

The lacunary T10 failure interface supplies fixed `A>=1`, arbitrarily large
`n`, and for every requested `K>=1` legal integers

\[
 N=16AnK,\quad 1\le r<N,\quad J=N-r\ge K,\quad
 1\le h\le256An                                             \tag{3.2}
\]

such that

\[
 \left|\sum_{j=0}^{J-1}e\bigl(h(10^r-1)10^j\pi\bigr)\right|
 >{J\over131072A^2n^2}.                                    \tag{3.3}
\]

For a rational transfer `theta`, spending half the threshold on approximation
requires

\[
 |\pi-\theta|\le
 {9J\over524288\pi A^2n^2h(10^r-1)(10^J-1)},              \tag{3.4}
\]

and leaves the exact cancellation target

\[
 \boxed{|L_{h(10^r-1),J}(\theta)|
 \le {J\over262144A^2n^2}.}                                \tag{F10}
\]

T28 instead needs adjacent rational data including

\[
 Q_0e_1+UQ_1e_0<1,\qquad e_0(q_{\rm cap})^8<CQ_0.          \tag{3.5}
\]

The lacunary T55 retains `TopShellCorrelationHypothesis`. Its direct-label T61
retains the strict variance inequality

\[
 V<\ell+2M_{\rm dir}-2B_{\rm pred}-2B_{\rm end}
       -{\ell\over4R\delta^2}.                             \tag{3.6}
\]

Lacunary T64 retains both its active-boundary estimate and

\[
 \|\operatorname{rowFourierRemainder}(\ell,P)\|
 \le {P^2\over10\,10^\ell},                               \tag{3.7}
\]

with cutoffs `40*10^(3*ell)` and `8000*10^(3*ell)`. The
positive-entropy T61 in Section 2 is a different theorem and namespace from
the lacunary direct-label T61 in (3.6).

## 4. Ranked decision table

| rank | candidate and normalized fingerprint | nearest closed branch | exact premise and applicability | all three programs and both reviews | displayed substitution and bounded discriminator | SUCCESS ENDPOINT | KILL ENDPOINT | disposition |
|---:|---|---|---|---|---|---|---|---|
| 1 | **Review B exact short-from-long charging:** universal overlap combinatorics at `L=b^floor(n/2)`, then global carry thickening | T83 exact-long subexponential sibling; PFE T61 signed short-sector premise | Conjecture (RB), quantified in Card 2. It does not bound the Vaaler majorant directly. With the exact-to-residual bridge, it would remove one real PFE T61 premise while retaining effective irrationality and residual-long linearity. No implication to lacunary T10/T28/T55/direct-label-T61/T64. | **PFE:** conditionally removes `SignedStructuredDenominatorPremise`, but PFE T86 supplies coefficient energy only. **Long-lag:** supplies no canonical `R_pi` bound; LL T87 leaves centered off-diagonal cancellation open. **NRS:** uses T7's comparison only and gives no canonical witness. **Review A:** its checked constant-run example is compatible but does not prove or refute RB. **Review B:** RB remains the conjecture under test. | `(RB)` gives `E<=(C_b+1)L+(5/2)R`, hence T7 gives `Q<=(3C_b+3)L+(15/2)R`. The generic-word replay finds `D_2(6)=41/8`, so any `C_2<41/8` is killed. | Prove (RB) with `C_b` depending only on `b`, machine-check exact `R<=longResidual` under effective irrationality, and derive PFE C7 without `SignedStructuredDenominatorPremise`. | An unbounded word family with `(S-(3/2)R)/L -> infinity`, any `n`-dependent constant, or a direct Vaaler-majorant inference kills the route. | Does not survive: unresolved universal lemma plus untouched fixed-pi long sector. |
| 2 | **Restricted irrationality:** upper-bound approximation only for `q=10^u(10^v-1)` | T18/T21/T81 scalar irrationality recycling, separated here by restricting the denominator family | Proof-sketch premise `nu_10(pi)<=M<mu_1`; definitions and source localization are in Card 1. It yields a strict superlinear factor-complexity sibling only. It supplies none of T7/T10/T28/T55/T61/T64. | **PFE:** strict superlinearity is below positive entropy. **Long-lag:** no collision estimate. **NRS:** no T7/T10 witness. **Review A / Review B:** their exact-collision claims neither imply nor follow from restricted approximation. | Localized Bugeaud--Kim replay gives `liminf p_pi(n)/n >= 1+Delta(M)`. Strictness is exactly `M<mu_1=2.246979...`. Substituting the sourced ordinary bound `7.103205...` gives `0.871745...<1`. | Prove a fixed-pi restricted theorem `nu_10(pi)<=M` for one explicit `M<mu_1`, with the all-but-finitely-many consequence matching the definition. | `M>=mu_1`, an ordinary bound only, a metric theorem, or bounded computation gives no strict improvement. | Does not survive: no fixed-pi restricted estimate reaches the threshold. |
| 3 | **Numerator-conductor cancellation:** replace modulus `m` by `m/gcd(a,m)` for the exact rational tails | T78/T79 rational-transfer branch, but with genuine numerator sensitivity rather than a modulus-only slogan | Bailey--Crandall Lemma 4.5, quantified in Card 3. Conditional on the T78/T79 notes' formulas, `a=h(10^r-1)u`. It can imply T10 only through (3.4) and (F10); it gives no T7/T28/T55/T61/T64 bridge. | **PFE:** no short-sector or grouped-phase bound. **Long-lag:** no exact-block collision bound and no centered critical-band estimate. **NRS:** direct T10 candidate only. **Review A / Review B:** their short-sector claims supply no numerator theorem and do not justify (RANGE), which is conditional only on the T78/T79/T85 arithmetic notes. | Exact applicability target is `t+sqrt(Q)(1+log Q)<=J/(262144A^2n^2)`. The legal T78 choice `r=1` leaves `gcd(a,m)<=9h<=2304An`; the T79 note's forced `P`-power likewise survives almost entirely; the T85 note's exceptional scale has empty coprime tail. | Prove the source hypotheses and the displayed target for **every** legal adaptive `(r,h)`, or prove a new theorem for the exact special numerators at `J asymp log m`. | One legal `(r,h)` for which the source theorem cannot certify (F10), an empty coprime tail, or an unproved special-numerator exclusion kills this theorem application. | Does not survive: the retained bound exceeds the logarithmic T10 budget. |

No fourth candidate is admitted. The fresh search screened recurrence-sensitive
prime-power sums, multiplicative-subgroup moments, semigroup dynamics, and
continued-fraction/integral approximants. Each either repeated a closed
rational-transfer/scalar fingerprint, required polynomial or
stretched-exponential length, averaged over numerators without locating the
T78/T79 numerator, or supplied density rather than a signed adaptive sum.
Retaining one as a “new direction” would rename a terminal hypothesis.

## 5. Card 1: localized Bugeaud--Kim threshold

For `q_(u,v)=10^u(10^v-1)`, define the restricted exponent

\[
 \nu_{10}(\pi)=\sup\{\tau:\
 \|q_{u,v}\pi\|<q_{u,v}^{1-\tau}
 \text{ for infinitely many }u,v\ge1\}.                  \tag{5.1}
\]

The definition is a `conjecture` interface for fixed pi, not a published
estimate. Bugeaud--Kim 2017, Lemma 3.6, constructs exactly denominators
`b^u(b^v-1)` when the exponent of repetition `rho` is below `2`. The 2026
paper repeats this at Lemma 4.1 and explicitly displays the restricted norm
inequality. Consequently, the following localization is a **proof sketch**
obtained by replaying their proof, not the wording of Theorem 1.4:

\[
 2\le M,\quad \nu_{10}(\pi)\le M
 \quad\Longrightarrow\quad
 \operatorname{rep}(d_1d_2\ldots)\ge {M\over M-1}.        \tag{5.2}
\]

Indeed, if `rho>=2`, (5.2) is immediate because `M/(M-1)<=2`. If `rho<2`,
the sourced construction gives
`nu_10(pi)>=rho/(rho-1)`, and this decreasing function gives (5.2).
The subsequent combinatorial part of the 2026 proof then gives

\[
 \liminf_{n\to\infty}{p_\pi(n)\over n}\ge1+\Delta(M),
 \quad
 \Delta(M)={-M^3+2M^2+M-1\over
 M^4-2M^3+3M^2-3M+1}.                                    \tag{5.3}
\]

For `M>=2` the denominator is positive. The numerator is positive precisely
for

\[
 2\le M<\mu_1=2.246979603717467\ldots,\qquad
 \mu_1^3-2\mu_1^2-\mu_1+1=0.                             \tag{5.4}
\]

The strict endpoint matters: `M=mu_1` gives no strict gain. The ordinary
irrationality exponent bounds the restricted one, but Zeilberger--Zudilin's
published `mu(pi)<=7.1032053341370017...` substituted into (5.3) gives
`1+Delta(M)=0.871745673849...`, weaker than the irrationality baseline.
Thus ordinary scalar irrationality cannot be recycled as success.

**Theorem-applicability card.** Object: fixed `pi`, base `10`, infinitely many
restricted denominators. Missing hypothesis: an upper bound below (5.4).
Published theorem used: Bugeaud--Kim's ordinary-`mu` complexity theorem plus
its source-visible restricted construction; localization status: proof sketch.
Named frontier: direct strict factor-complexity sibling only; none of
T7/T10/T28/T55/T61/T64.

**SUCCESS ENDPOINT.** A fixed-pi theorem gives `nu_10(pi)<=M` for an explicit
`M<mu_1`, with the quantifiers in (5.1).

**KILL ENDPOINT.** `M>=mu_1`, an ordinary or metric estimate only, or bounded
computation does not make (5.3) strictly exceed one.

**Smallest discriminating calculation.** Evaluate the cubic at a proposed
`M` and evaluate (5.3). Success is strict positivity. Kill is nonpositivity.
`verify_note.py` checks the root interval, equality threshold, and the sourced
ordinary-bound substitution without using pi digits.

## 6. Card 2: exact equality versus carry-thickened Vaaler

Fix `b>=2`, `n>=1`, and `L=b^floor(n/2)`. For every word `x` of length at
least `L+n-1`, let

\[
 S_x^=(n,L)=\#\{(i,j)<L:0<|i-j|<n,\ x[i,i+n)=x[j,j+n)\}, \tag{6.1}
\]

\[
 R_x^=(n,L)=\#\{(i,j)<L:|i-j|\ge n,\ x[i,i+n)=x[j,j+n)\}. \tag{6.2}
\]

Both are ordered and off-diagonal. The useful exact reading of Review B is
the following still-unproved `conjecture`:

\[
 \boxed{\forall b\ge2\ \exists C_b\ge0\ \forall n\ge1\
 \ \forall x:\quad S_x^\le C_bL+{3\over2}R_x^=.}          \tag{RB}
\]

For the decimal pi word, exact collision energy satisfies

\[
 E_\pi(n,L)=L+S_\pi^=(n,L)+R_\pi^=(n,L).                 \tag{6.3}
\]

Therefore (RB) gives

\[
 E_\pi(n,L)\le(C_{10}+1)L+{5\over2}R_\pi^=(n,L),         \tag{6.4}
\]

and the actual carry-thickened T7 comparison (3.1) gives

\[
 \boxed{Q_\pi(n,L)\le(3C_{10}+3)L+{15\over2}R_\pi^=(n,L).}
 \tag{6.5}
\]

This is the exact frontier substitution. If effective irrationality excludes
every arithmetic-excluded exact long collision and the retained PFE
`SparseLongResidualLinearBound` supplies
`longResidualPairCount<=K L`, then the additional bridge

\[
 R_\pi^=(n,L)\le\operatorname{longResidualPairCount}(n,L) \tag{6.6}
\]

would make (6.5) a short-residual linear bound with constant

\[
 A=3C_{10}+3+{15\over2}K.                                 \tag{6.7}
\]

Consequently (RB), (6.6), effective irrationality, and residual-long
linearity would reach the positive-entropy program's C7 **without** its
`SignedStructuredDenominatorPremise`. This is a real conditional hypothesis
removal. It is not a fixed-pi conclusion because (RB), (6.6), and the long
bound are not supplied here.

There is no direct Vaaler substitution. The accepted theorem has direction

\[
 \operatorname{strictResidualIncidenceCount}
 \le\operatorname{structuredVaalerMajorantTotal}.         \tag{6.8}
\]

An upper incidence bound cannot upper-bound the majorant in (6.8). The valid
conditional route is global charging (6.3)--(6.7), not reversal of (6.8).
Likewise PFE T86's `D_N<42` bounds grouped coefficients, not their actual
fixed-pi phase pairing. It does not prove (RB), (6.6), or the long bound.

**Theorem-applicability card.** Statistic: exactly `L` starts, both
orientations, no diagonal, short cutoff `<n`, long cutoff `>=n`. Review B is a
conjecture. Removed premise if all bridges are proved: PFE
`SignedStructuredDenominatorPremise`. Retained premises: effective
irrationality and sparse residual-long linearity. Named lacunary frontiers:
no T10, T28, T55, direct-label T61, or T64 implication.

**SUCCESS ENDPOINT.** Prove (RB) with `C_b` depending only on `b`, prove (6.6),
and machine-check the PFE C7 bridge with the constant (6.7).

**KILL ENDPOINT.** An unbounded family for (6.9), a constant depending on the
word or `n`, or an attempted reversal of (6.8) kills the proposed use.

**Smallest bounded discriminating calculation.** Define

\[
 D_b(n)=\max_x{2S_x^=-3R_x^=\over2L}.                     \tag{6.9}
\]

Exhausting all binary words for `1<=n<=6` gives
`D_2(n)=0,1,1,3,3,41/8`. At `n=6,L=8`, a maximizer has
`S=50,R=6`, forcing `C_2>=41/8`. This is an `experiment` on generic finite
words only. It can kill a proposed explicit constant but cannot prove the
existence of `C_b`.

## 7. Card 3: exact T78/T79 numerator conductors

This card is conditional on the unverified T78/T79 notes' rational-tail
formulas. In the T78 notation the claimed reduction is

\[
 q_K=5^{e_K}m_K,\quad(m_K,10)=1,\quad
 u_K\equiv p_K2^{e_K}\pmod {m_K},\quad
 a_{78}\equiv h(10^r-1)u_K\pmod {m_K},                   \tag{T78-family}
\]

and the coprime tail begins after `e_K`. In the T79 notation it is

\[
 q_E=2^{a_E}5^{b_E}m_E,\quad(m_E,10)=1,\quad
 t_E=\max(a_E,b_E),
\]

\[
 u_E\equiv p_E2^{t_E-a_E}5^{t_E-b_E}\pmod {m_E},\quad
 a_{79}\equiv h(10^r-1)u_E\pmod {m_E},                  \tag{T79-family}
\]

and the coprime tail begins after `t_E`. Thus both claimed tails have the
normalized form

\[
 \sum_{s=0}^{J-t-1}e\left({a10^s\over m}\right),\qquad
 a=h(10^r-1)u,\quad (u,m)=1,
 \tag{7.1}
\]

where `t` is the power-of-2/5 transient. The phrase `J asymp log m` is used
only under the notes' explicit balanced-schedule conditions

\[
 E=\Theta(N+n),\quad n=O(N),\quad N<E,\quad
 \log m=\Theta(E),
 \quad\Longrightarrow\quad J\le N=\Theta(\log m).        \tag{RANGE}
\]

Without all four conditions, no logarithmic range is inferred from transfer
alone.

Bailey--Crandall Lemma 4.5 fixes
coprime integers `b,c>1`. Write `c=product_i p_i^t_i`, put
`tau_1=ord_(p_1*...*p_s)(b)`, and let `epsilon=1` exactly when `c` is even,
`tau_1` is odd, and `b=3 (mod 4)`; otherwise let `epsilon=0`. Define `beta_i`
by

\[
 p_i^{\beta_i}\Vert b^{(\epsilon+1)\tau_1}-1,\qquad
 c_1(c)=\prod_i p_i^{\min(t_i,\beta_i)}.                  \tag{7.2}
\]

For a source sum of length `ell`, the lemma puts `d=gcd(H,c)`, assumes

\[
 d<c/c_1(c),\qquad1\le \ell\le\operatorname{ord}_c(b),    \tag{7.3}
\]

and proves

\[
 \left|\sum_{j=0}^{\ell-1}e(Hb^j/c)\right|
 <\sqrt{c/d}\,(1+\log(c/d)),                              \tag{7.4}
\]

where `log` is the natural logarithm.
Thus this is genuinely numerator-sensitive through the additive conductor
`Q=c/d`. Including a trivially bounded transient, its exact sufficient T10
certificate is

\[
 \boxed{t+\sqrt Q(1+\log Q)
 \le {J\over262144A^2n^2}.}                               \tag{7.5}
\]

For (7.1), the exact source substitution is

\[
 b=10,\quad c=m,\quad H=a,\quad d=\gcd(a,m),\quad
 \ell=J-t,
\]

so a nonempty tail requires `t<J` and the source length condition is exactly

\[
 1\le J-t\le\operatorname{ord}_m(10).                     \tag{7.3a}
\]

All of `(m,10)=1`, (7.3), (7.3a), transfer (3.4), and (7.5) must hold for
every legal adaptive pair that T10 may return. If `J<=t`, the tail is empty
and the entire length `J` is charged trivially, which cannot meet F10.

For the T78 family, the legal choice `r=1` gives

\[
 d=\gcd(9h,m)\le9h\le2304An.                              \tag{7.6}
\]

Conditional on the T78 note's exponentially large transferred modulus, the
conductor remains exponential while the right side of (7.5) is polynomial.
This kills this **theorem application**, not the possibility that the actual
special sum cancels.

For the T79 family, conditionally on its stated-range forced factor
`P^E|m`, `P=147153121`, the note's order and LTE formulas give only
`v_P(gcd(a,m))=O(log E)` in the balanced `J,N=Theta(E)` range. Hence
`Q>=P^(E-O(log E))`, again far outside (7.5). The T85 note's exceptional
configuration `E=P^2+2` instead has `t=E` while transfer forces `J<N<E`, so
the coprime tail (7.1) is empty. Each sentence in this paragraph remains
conditional on those notes' unformalized arithmetic claims.

**Theorem-applicability card.** Source theorem: (7.2)--(7.4). Actual objects:
composite T78/T79 tail modulus and exact adaptive numerator (7.1). Missing:
small conductor for every legal `(r,h)`, order range, and a nonempty tail.
Named implication: T10 only, through (3.4) and (7.5). No T7/T28/T55/T61/T64
implication.

**SUCCESS ENDPOINT.** Verify coprimality, (7.3), (7.3a), transfer (3.4), and
(7.5) for every legal adaptive `(r,h)`, or obtain a theorem for the exact
numerators at logarithmic length.

**KILL ENDPOINT.** A failed source hypothesis, empty coprime tail, or one legal
adaptive pair whose source bound cannot certify F10 kills this application.

**Smallest discriminating calculation.** Compute `d=gcd(a,m)`, `Q=m/d`,
the transient `t`, and both sides of (7.5) for the first candidate scale and
the legal case `r=1`. Success is (7.3) plus (7.5). Kill is a failed source
hypothesis, empty tail, or source upper bound above the F10 budget. The
universal symbolic bound (7.6), not a sample of pi digits, already kills a
uniform certificate whenever the note's exponential-modulus premise holds.

## 8. Cross-frontier closure

Candidate 1 conditionally replaces one PFE T61 input, but neither proves the
exact-long fixed-pi bound nor controls the Vaaler expression. Candidate 2 is a
strict factor-complexity sibling and never reaches a retained near-return or
Fourier frontier. Candidate 3 is the only direct T10 candidate and fails the
source theorem's conductor/length applicability. None supplies T28's adjacent
compatibility, T55's top-shell correlation, lacunary T61's strict variance, or
T64's boundary and row-remainder estimates.

The two newest machine-checked deterministic opportunities do not change this
classification: PFE T86 bounds coefficient energy before fixed-pi phase
pairing, and long-lag T87 bounds the record diagonal while leaving the centered
off-diagonal term. Proposing phase decorrelation or centered cancellation as a
new premise would merely rename the terminal hypotheses identified by the
semantic memory.

Reproduction from a directory containing only these artifacts:

```text
python3 verify_note.py
sha256sum -c SHA256SUMS
```

The replay checks all vendored hashes and source anchors, the source and
candidate caps, the cubic and correction thresholds, the collision constants,
the bounded generic-word discriminator, the exact T10 budget constants, every
success/kill marker, and the unique final decision. Its bounded computations
are transcription checks, never evidence for a universal or fixed-pi claim.

TERMINAL DECISION (1/1): SOURCE-PINNED NEGATIVE SYNTHESIS. Park C1, C2, G11, and G19; do not schedule another representation scout. Reopen only after independent verification of one displayed SUCCESS ENDPOINT; no follow-up is ranked or scheduled.
