# T86: bounded post-T85 pi-specific mechanism audit

Date: 2026-08-09 UTC.

Status: `literature-checked` bounded source audit plus displayed derivations.
No new Lean theorem is claimed. Finite replay checks are `experiment` evidence
only. This report proves no C1, C2, canonical near-return estimate, normality,
equidistribution, or decimal-digit assertion for pi.

## 1. Immutable target and ambiguities

The delivered `canonical_statement.txt` is byte-exact and has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

For integers `n,N>=1`, the target is

\[
 Q_\pi(n,N)=\#\{(i,j):0\le i,j<N,
 \|(10^i-10^j)\pi\|_{\mathbb R/\mathbb Z}<10^{-n}\}.
\tag{1.1}
\]

Pairs are ordered, the diagonal is included, and the inequality is strict.
The exact canonical quantifiers are

\[
 \forall A\ge1\ \exists n_0\ge1\ \forall n\ge n_0\ \exists N\ge1:
 A n Q_\pi(n,N)\le N^2.
\tag{1.2}
\]

`N` may depend on `A,n`. No infinitely-many-depth, fixed-`A`, prescribed-`N`,
off-diagonal, unordered, non-strict, other-base, almost-everywhere, or finite
experiment sibling is substituted.

## 2. Audit protocol, labels, and caps

The search used Crossref, OpenAlex, DOI/publisher records, and the accepted
local library on 2026-08-09. It screened effective multiplicative dynamics,
pi-specific complex integrals, continued fractions/products, AGM/modular
methods, hypergeometric transformations, q-series, spectral products, and
congruence methods. It is a bounded opportunity search, not an assertion that
all mathematical literature has been exhausted.

Exactly three candidates and four primary sources are retained:

| candidate | mechanism | primary sources |
|---|---|---:|
| CANDIDATE 1 | effective `x2,x5` semigroup specialized to pi | 2 |
| CANDIDATE 2 | Hata complex-integral Gaussian rational approximants | 1 |
| CANDIDATE 3 | Wallis/Brouncker rational sequence | 1 |

The labels used below have disjoint meanings.

- **SOURCE THEOREM:** a theorem or formula at the exact locator in
  `SOURCE_PINS.md`.
- **DERIVATION:** an argument displayed in this report from sourced or
  elementary premises.
- **CONJECTURE:** an explicitly unproved mathematical premise.
- **HEURISTIC:** scale intuition not used as proof.
- **EXPERIMENT:** bounded replay checks, never evidence for a universal claim.

There are no conjectural premises in the terminal negative map. Whenever an
unproved estimate is described as sufficient, it is labeled **CONJECTURE** and
is not treated as progress.

## 3. Accepted fixed-pi frontiers

The six byte-vendored Lean files and hashes are listed in `SOURCE_PINS.md`.
They are accepted machine-checked interfaces. None asserts its conditional
pi-specific cancellation premise.

### 3.1 T7 finite cylinder energy

**SOURCE THEOREM (machine-checked).** T7 proves

\[
 E_\pi(n,N)\le Q_\pi(n,N)\le3E_\pi(n,N)
\tag{3.1}
\]

and makes (1.2) equivalent to the same eventual quantifier pattern with
`E_pi`. A candidate must therefore give an upper collision-energy witness, not
one dense point or one finite orbit.

### 3.2 T10 long-lag resonance

**SOURCE THEOREM (machine-checked).** Literal failure of (1.2) gives one
`A>=1`, arbitrarily large `n`, and, for every requested `K>=1`, legal `N,r,h`
with

\[
 N=16AnK,\qquad 1\le r\le N-1,\qquad
 K\le J=N-r,\qquad 1\le h\le256An,
\tag{3.2}
\]

and

\[
 {J\over131072A^2n^2}<
 \left|\sum_{j=0}^{J-1}
 e\bigl(h(10^r-1)10^j\pi\bigr)\right|,
 \qquad e(x)=\exp(2\pi i x).
\tag{3.3}
\]

This is a sufficient contradiction target, not a reformulation of (1.2).

### 3.3 T28, T55/T61, and T64

**SOURCE THEOREMS (machine-checked, conditional).** T28 requires adjacent
approximants satisfying, among other clauses,

\[
 Q_0e_1+UQ_1e_0<1,
 \qquad e_0(q_{\rm cap})^8<CQ_0.
\tag{3.4}
\]

T55 requires its strict `TopShellCorrelationHypothesis`. T61 requires

\[
 V<\ell+2M_{\rm dir}-2B_{\rm pred}-2B_{\rm end}
       -{\ell\over4R\delta^2}.
\tag{3.5}
\]

T64 requires, for `q=10^ell`, both a boundary count and

\[
 \|\operatorname{rowFourierRemainder}(\ell,P)\|
 \le {P^2\over10q},
\tag{3.6}
\]

with frequency cutoffs `40q^3` and `8000q^3`. A bibliography, density theorem,
or phase approximation does not discharge (3.4)--(3.6).

## 4. Common exact T10 transfer budget

Put

\[
 c=h(10^r-1),\qquad
 L_{c,J}(\theta)=\sum_{j=0}^{J-1}e(c10^j\theta).
\tag{4.1}
\]

**DERIVATION.** The elementary inequality
`|e(x)-e(y)|<=2*pi*|x-y|` and geometric summation give

\[
 |L_{c,J}(\pi)-L_{c,J}(\theta)|
 \le {2\pi c(10^J-1)\over9}|\pi-\theta|.
\tag{4.2}
\]

To spend half of the T10 threshold on approximation, define

\[
 \boxed{\varepsilon_{10}(A,n,N,r,h)=
 {9J\over524288\pi A^2n^2h(10^r-1)(10^J-1)}}.
\tag{4.3}
\]

Then `|pi-theta|<=epsilon_10` makes (4.2) at most
`J/(262144 A^2 n^2)`. A successful transferred candidate would still have to
prove the other half:

\[
 \boxed{|L_{c,J}(\theta)|\le {J\over262144A^2n^2}.}
\tag{F10}
\]

With (4.2), (F10) would contradict (3.3). Thus (F10), with the literal
adaptive range (3.2), is the named kill inequality for rational-transfer
candidates. It is not assumed below.

The largest phase coefficient is bounded by

\[
 c10^{J-1}<256An\,10^{r+J}=256An\,10^N.
\tag{4.4}
\]

This exponential coefficient range is retained in every comparison.

## 5. Candidate 1: effective times-2, times-5 dynamics

### 5.1 Exact sourced theorem and pi specialization

**SOURCE THEOREM.** BLMV Theorem 1.8 fixes multiplicatively independent
integers `a,b>1`. If an irrational `alpha` has some `k` such that

\[
 |\alpha-p/q|\ge q^{-k}
 \quad(q\ge2,\ p\in\mathbb Z),
\tag{5.1}
\]

then there are `kappa_6=kappa_6(a,b)>0` and `N0=N0(k,a,b)` such that

\[
 \{a^s b^t\alpha:0\le s,t\le X\}
 \text{ is }(\log\log X)^{-\kappa_6}\text{-dense}
\tag{5.2}
\]

for every `X>=N0`. The theorem supplies density, not discrepancy or a signed
sum estimate.

**SOURCE THEOREM.** Zeilberger--Zudilin prove
`mu(pi)<36/5`. Choosing epsilon `4/5` in their definition gives an
existential `Q8` such that

\[
 q\ge Q_8\Longrightarrow |\pi-p/q|>q^{-8}
 \quad(p\in\mathbb Z).
\tag{5.3}
\]

No numerical `Q8` is supplied.

**DERIVATION.** Fix legal integers `h,r` and put

\[
 \alpha_{h,r}=h(10^r-1)\pi,\qquad a=2,\quad b=5.
\tag{5.4}
\]

Equation (5.3), irrationality of `alpha_(h,r)`, and a finite minimum over the
remaining denominators imply that some exponent `k=k(h,r)` makes (5.1) true.
Thus (5.2) applies separately to each fixed `(h,r)`. Neither `k` nor `N0` is
uniform over T10's adaptive family.

### 5.2 Parameter map

The BLMV box and the T10 diagonal are

\[
 B_X=\{2^s5^t\alpha_{h,r}:0\le s,t\le X\},\qquad
 D_J=\{2^j5^j\alpha_{h,r}:0\le j<J\}.
\tag{5.5}
\]

| parameter | sourced or derived value |
|---|---|
| coefficient growth | (4.4), exponential in `N` |
| denominator/modulus | not applicable; theorem acts on the real orbit |
| orbit size | at most `(X+1)^2` in the box; exactly `J` labels on the required diagonal |
| multiplicative order | not applicable |
| truncation error | zero |
| sourced occupancy range | one-point density at radius `(log log X)^(-kappa_6)` in the full box |
| required range | diagonal signed cancellation (F10), or T7 pair occupancy at radius `10^-n` |

**DERIVATION.** Merely forcing the source resolution below the decimal radius
requires

\[
 (\log\log X)^{-\kappa_6}\le10^{-n}
 \quad\Longrightarrow\quad
 X\ge\exp\!\bigl(\exp(10^{n/\kappa_6})\bigr).
\tag{5.6}
\]

Even at (5.6), (5.2) gives a hit somewhere among two independent indices; it
gives no count and no information on `s=t`.

BLMV Theorem 1.4 is also inapplicable as a shortcut. Applied to an empirical
decimal-orbit measure, it assumes `H_mu(P^X)>=rho log X`. That is positive
cylinder spreading of the kind T7/T64 asks a pi-specific mechanism to prove;
using it here would be circular.

### 5.3 First failed inequality and kill criterion

**FAILED FRONTIER INEQUALITY (T10).** The source gives no implication of the
form

\[
 |L_{h(10^r-1),J}(\pi)|
 \le {J\over262144A^2n^2}
\tag{5.7}
\]

for any T10-uniform range, nor any diagonal discrepancy from which (5.7)
follows. Density of `B_X` does not bound a sum over `D_J`.

**SMALLEST KILL TEST.** Read Theorems 1.4 and 1.8 at the pinned pages: both
select or control arbitrary products `2^s5^t`; neither restricts to `s=t`,
counts diagonal visits, or estimates a diagonal character sum. Failure of that
statement-level test kills this candidate before any computation.

**VERDICT.** Genuinely distinct semigroup input, quantitatively negative due
to the two-parameter-box/decimal-diagonal gap and nonuniform Diophantine
constants.

## 6. Candidate 2: Hata complex-integral approximants

### 6.1 Exact sourced statement

**SOURCE THEOREM.** Hata Theorem 1.1 states that for every `epsilon>0` there
is `H0(epsilon)` such that, for all integers `p,q,r` with
`H=max(|q|,|r|)>=H0`,

\[
 |p+q\pi+r\log2|\ge H^{-\mu-\epsilon},
 \qquad \mu=7.016045\ldots.
\tag{6.1}
\]

**SOURCE CONSTRUCTION.** On printed pp. 344--345, Hata constructs Gaussian
integers `p_s,q_s,r_s` with

\[
 q_s\pi-p_s=\epsilon_s,
\quad {1\over s}\log|q_s|\to\sigma>0,
\quad {1\over s}\log|\epsilon_s|\to-\tau<0,
\quad {\sigma\over\tau}=\mu.
\tag{6.2}
\]

All quantifiers here are asymptotic as integer `s->infinity`; the source gives
no base-10 modular theorem for these forms.

### 6.2 Rational extraction and transfer

**DERIVATION.** Write `q_s=a_s+ib_s`, `p_s=c_s+id_s`, and choose the component
`Q_s` of `q_s` having larger absolute value, with matching component `P_s`.
Then

\[
 |Q_s|\ge {|q_s|\over\sqrt2},\qquad
 \left|\pi-{P_s\over Q_s}\right|
 \le {\sqrt2|\epsilon_s|\over|q_s|}.
\tag{6.3}
\]

For every fixed `delta` with `0<delta<min(sigma,tau)/2`, (6.2) implies that
for all `s>=s_delta`, where the finite source-asymptotic threshold `s_delta`
is not numerically supplied,

\[
 \left|\pi-{P_s\over Q_s}\right|
 \le\sqrt2e^{-(\sigma+\tau-2\delta)s},
 \qquad |Q_s|\le e^{(\sigma+\delta)s}.
\tag{6.4}
\]

Thus (4.3) is guaranteed by the sufficient schedule

\[
 s\ge\max\left(s_\delta,
 \left\lceil{\log(\sqrt2/\varepsilon_{10})
       \over\sigma+\tau-2\delta}\right\rceil\right).
\tag{6.5}
\]

For fixed `delta`, choose the least integer allowed by (6.5). Once
`epsilon_10` is small enough that the logarithmic term dominates `s_delta`,
(6.4) gives

\[
 |Q_s|\le C_\delta
 \varepsilon_{10}^{-(\sigma+\delta)/(\sigma+\tau-2\delta)},
 \qquad C_\delta=e^{\sigma+\delta}(\sqrt2)^{
 (\sigma+\delta)/(\sigma+\tau-2\delta)}.
\tag{6.6}
\]

The exponent tends, as `delta` decreases to zero, to
`sigma/(sigma+tau)=mu/(mu+1)=0.875250...`. This is an asymptotic family of
upper exponents, not an effective uniform schedule at `delta=0`.

Reduce `P_s/Q_s=p'_s/q'_s` with `q'_s>0`, and put

\[
 t_s=\max(v_2(q'_s),v_5(q'_s)),\quad
 m_s={q'_s\over2^{v_2(q'_s)}5^{v_5(q'_s)}},\quad
 d_s=\operatorname{ord}_{m_s}(10)
\tag{6.7}

when `m_s>1` (and `d_s=1` when `m_s=1`).

| parameter | sourced or derived value |
|---|---|
| coefficient growth | (4.4) |
| denominator size | fixed-`delta` upper bound (6.6); eventual irrationality gives only a scalar lower bound |
| decimal transient | `t_s`; source gives no valuation or reduction law |
| orbit length/order | `d_s`; source gives no lower bound or usable factorization |
| truncation error | (6.4)--(6.5) |
| required range | all adaptive `h,r,J` in (3.2), through (F10) |
| occupancy/exponential sum | absent from the source |

The crude bound `t_s<=log_2 q'_s=O(N+log(An))` allows the transient to consume
the complete length `J`. This is a possibility, not an assertion that it
always occurs.

### 6.3 First failed inequality and kill criterion

**FAILED FRONTIER INEQUALITY (T10).** After spending half the threshold via
(6.5), the first missing statement is exactly

\[
 \left|\sum_{j<J}e\left(
 {h(10^r-1)10^jp'_s\over q'_s}\right)\right|
 \le {J\over262144A^2n^2}.
\tag{6.8}
\]

Neither Theorem 1.1 nor the construction on pp. 344--345 states a valuation,
order, occupancy, or exponential-sum bound. Equation (6.8) is therefore not a
consequence of the retained source.

**SMALLEST KILL TEST.** Search the pinned theorem and construction for a
quantifier uniform in base-10 powers or a character-sum estimate. Their only
outputs are linear-form lower bounds and coefficient/error asymptotics. The
absence of (6.8) kills the route before T28, T55/T61, or T64 can be invoked.

**VERDICT.** Reject as scalar rational-approximation transfer. Different
integrals and a better error exponent do not supply the source-pinned base-10
control required to escape T63/T78/T79/T81/T85.

## 7. Candidate 3: Wallis/Brouncker rational sequence

### 7.1 Exact sourced theorem and rational arithmetic

**SOURCE FORMULA.** Lin--Deng--Chen equations (1.1)--(1.2) define

\[
 W_s=\prod_{k=1}^s{4k^2\over4k^2-1}\longrightarrow{\pi\over2}.
\tag{7.1}
\]

Their equation (3.11) gives

\[
 W_s={\pi\over2}\left(1-{1\over4s}+{5\over32s^2}
 +O(s^{-3})\right).
\tag{7.2}
\]

**DERIVATION.** Direct product cancellation gives the exact rational
approximant

\[
 \theta_s=2W_s=
 {2^{4s+1}\over(2s+1){2s\choose s}^2}={p_s\over q_s}
\tag{7.3}
\]

in lowest terms after removing the complete power of two from the displayed
denominator. Thus

\[
 q_s=\operatorname{oddpart}\left((2s+1){2s\choose s}^2\right).
\tag{7.4}
\]

Equation (7.2) has the exact quantified consequence

\[
 \exists s_0\ \forall s\ge s_0:
 {1\over2s}<\pi-\theta_s<{1\over s}.
\tag{7.5}
\]

Hence transfer at (4.3) necessarily requires

\[
 s>{1\over2\varepsilon_{10}},
\tag{7.6}
\]

and `s>=1/epsilon_10` is eventually sufficient.

### 7.2 Denominator, transient, and order

Put

\[
 t_s=v_5(q_s),\qquad m_s=q_s/5^{t_s},\qquad
 d_s=\operatorname{ord}_{m_s}(10).
\tag{7.7}

There is no power-of-two transient because `q_s` is odd.

**DERIVATION.** Legendre's formula gives
`v_p(n!)=sum_{a>=1} floor(n/p^a)`. Therefore
`v_p(C(2s,s))` is at most the number of base-`p` digits of `s`. Also

\[
 {2s\choose s}\ge{4^s\over2s+1},
\tag{7.8}
\]

because the central coefficient is the largest among `2s+1` nonnegative
coefficients summing to `4^s`. Removing the 2- and 5-parts from the displayed
denominator in (7.3) consequently gives the explicit coarse bound

\[
 \boxed{m_s\ge {16^s\over100s^4(2s+1)^2}.}
\tag{7.9}
\]

The elementary upper bound `{2s choose s}<=4^s` also gives

\[
 m_s\le(2s+1)16^s.
\tag{7.10}
\]

Thus `log m_s=Theta(s)`. Combining (7.6), (4.3), and the exact T10 identity
`r+J=N`, the required transfer scale has `s` at least a constant multiple of
`10^N/J`, apart from the displayed positive polynomial factors. Hence, as the
requested `K` and therefore `J` tend to infinity,

\[
 J=O(\log\log m_s)
\tag{7.11}
\]

uniformly over legal positive `A,n,h,r`. This is even shorter than the
qualified logarithmic-modulus comparison recorded in the T85 note.

| parameter | sourced or derived value |
|---|---|
| coefficient growth | (4.4) |
| denominator/modulus | exact (7.4), bounds (7.9)--(7.10) |
| decimal transient | `t_s=O(log s)`; it may still be comparable to `J` |
| multiplicative order | exact definition `d_s`, no source lower bound |
| truncation error | two-sided (7.5); required index (7.6) |
| required range | special numerator, base 10, length `J=O(log log m_s)` from (7.11) |
| occupancy/exponential sum | not estimated by the source |

Any rational-orbit theorem with a positive `sqrt(m_s)` leading cost is
trivial here, since (7.9) and (7.6) eventually make `sqrt(m_s)>J`. This is a
route-specific comparison, not a universal lower bound for every possible
structure-sensitive estimate.

### 7.3 First failed inequality and kill criterion

**FAILED FRONTIER INEQUALITY (T10).** The first missing assertion is

\[
\left|\sum_{j<J}e\left(
 {h(10^r-1)10^jp_s\over q_s}\right)\right|
 \le {J\over262144A^2n^2}
\tag{7.12}
\]

at the double-logarithmic modulus length (7.11). Wallis asymptotics estimate
`pi-theta_s`; they do not estimate (7.12). Period and equality collisions do
not imply signed cancellation.

**SMALLEST KILL TEST.** Equation (7.2) plus the exact denominator (7.4)
already yields (7.6)--(7.11). Any proposed generic square-root-modulus bridge
is killed by checking `sqrt(m_s)>J`. A different bridge survives this first
size check only if its primary theorem explicitly treats the actual numerator,
base 10, pretransient, and double-logarithmic length. The retained source has
no such theorem.

**VERDICT.** Reject as a nonfactorial instance of the already exhausted
rational approximation/modular-orbit semantic route, with a strictly worse
usable length than T85's logarithmic frontier.

## 8. Semantic fingerprint against T63/T68/T78/T79/T80/T81/T82/T85

The status column prevents an unverified note from becoming a premise. Rows
marked `proof sketch` are comparison inventory only.

| item | verification level | semantic fingerprint and decisive boundary | T86 disposition |
|---|---|---|---|
| T63 | literature-checked applicability audit | BBP/Zudilin formulas and Bailey--Crandall rational phases give no adaptive base-10 T55/T61 cancellation; the direct common denominator has fatal square-root cost | C2 and C3 reproduce rational transfer without a new base-10 theorem, so reject; C1 is genuinely different |
| T68 | machine-checked route-specific Lean result | removing Zudilin's `5^e` transient forces `J<2K-1` while a positive tail requires `2K-1+extra<J` | no candidate reuses Zudilin; C2/C3 still lack their own transient theorem |
| T78 | proof sketch, source audit literature-checked | Euler--Li factorial truncations have exact order/occupancy but accurate transfer forces `sqrt(m_K)>N` | C3 is nonfactorial but has the same rational-orbit scale failure (7.9)--(7.12); reject renamed route |
| T79 | proof sketch | in T79's stated range `E<P`, Abrarov--Quine rational arctangent truncations have a forced prime-power modulus and square-root cost above T10 length; T85 requires a tie/residue audit outside that range | C2/C3 use different formulas but terminate at the same missing special-numerator sum; reject |
| T80 | proof sketch | Ramanujan reciprocal truncations lie in `Q(sqrt 2)`; finite ideal order is not a period for the real character modulo `Z` | none uses an algebraic quotient; C1 remains distinct, while no algebraic workaround is claimed |
| T81 | proof sketch using machine-checked T73/T28 inputs | scalar irrationality packing allows `Q^7` capacity at exponential coefficient height and supplies neither T28 inequality | (5.3) is used only to meet BLMV's fixed-point Diophantine premise; no scalar packing progress is claimed; C2 is rejected as scalar |
| T82 | proof sketch using machine-checked T64 input | Chudnovsky certification states expand by factor 10 and do not prove T64's tensor/boundary premises | none uses certification carries; C1's entropy shortcut is rejected as circular rather than renamed carry control |
| T85 | proof sketch adversarial correction | valuation ties require residue audit; at one T79 scale the transient consumes the prefix; the note's all-numerator counterexample does not exclude special numerators | C2 has uncontrolled reduction/transient; C3 needs still shorter `O(log log m)` special-numerator cancellation; this row is comparison inventory, while rejection independently rests on absence of (6.8)/(7.12) in the retained sources |

This table rejects standard BBP/Zudilin, factorial, Abrarov--Quine
arctangent, Ramanujan--Sato denominator-ideal, scalar irrationality-packing,
and Chudnovsky carry-certification routes unless a new primary theorem supplies
the missing base-10 control. No such theorem was found in this bounded search.

## 9. Candidate-complete quantitative negative map

| rank in bounded audit | candidate | named frontier | first failed quantitative statement | decisive reason |
|---:|---|---|---|---|
| 1 | effective `x2,x5` dynamics | T10, with T7/T64 also inspected | diagonal upper bound (5.7) | source controls density of a two-parameter box only; constants are not uniform in adaptive `(h,r)` |
| 2 | Hata complex integrals | T10 | rational-phase bound (6.8) after successful transfer (6.5) | source controls scalar linear forms, not reduced valuations, order, occupancy, or base-10 sums |
| 3 | Wallis/Brouncker | T10 | special-numerator bound (7.12) at `J=O(log log m_s)` | sourced error forces exponential truncation index and enormous modulus; no theorem reaches the required short sum |

The ranking measures proximity to a semantically new bridge, not mathematical
progress: all three are killed. Candidate 1 is genuinely different but lacks
diagonal restriction. Candidates 2 and 3 are candidate-complete negative
instances of explicitly excluded rational-transfer fingerprints. No candidate
supplies T28's cross-numerator inequalities, T55's top-shell correlation,
T61's strict variance margin, or T64's boundary and Fourier bounds.

## 10. Non-claims and replay

Run from a directory containing only these delivered artifacts:

```text
python3 verify_note.py
sha256sum -c SHA256SUMS
```

The verifier checks all source/frontier hashes, PDF text anchors, theorem
anchors, candidate/source caps, exact Wallis rational identities at bounded
indices, transfer constants, semantic-table coverage, and the unique terminal
line. Those bounded checks are `experiment` evidence for transcription only.
The universal derivations are the numbered arguments above.

There is no ranked surviving direction and no scheduled follow-up. A future
source can reopen this parked search only by passing the relevant displayed
kill inequality with all adaptive quantifiers; its existence is not conjectured
here.

TERMINAL ENDPOINT: CANDIDATE-COMPLETE QUANTITATIVE NEGATIVE MAP.
