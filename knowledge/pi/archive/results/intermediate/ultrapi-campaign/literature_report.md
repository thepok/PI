# Fixed-π disjunctivity audit: T40–T43 and 2025–2026 literature

Audit date: **2026-08-12 UTC**  
Audit status: `literature-checked`  
Target source: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target source SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Outcome

The intended target is the following finite-word statement, not a statement
about arbitrary infinite sequences:

\[
  \forall m\ge 0\;\forall a<10^m\;\exists n\ge 0:\quad
  \lfloor 10^m\{10^n\pi\}\rfloor=a.
\]

Equivalently, every finite decimal word, including words with leading zeroes,
occurs in the decimal expansion of \(\pi\). T41 additionally proves that this is
equivalent to every such cylinder being hit arbitrarily late. This target is
`conjecture`. It is disjunctivity and is strictly weaker than base-10
normality.

No complete proof, no theorem that specializes to a complete proof, and no
unconditional implication from T40–T43 to even one prescribed missing decimal
cell was found. The most relevant 2025–2026 results give only linear or
superlinear factor-complexity lower bounds, exceptional near-integer
finiteness for algebraic S-unit expressions, or distribution averaged over
all inputs at one fixed prime. None controls the one deterministic
fixed-\(\pi\) orbit, or its one selected residue at each changing composite
modulus.

The only additional implication recovered in the adversarial pass is the
already-recorded, gap-free `proof sketch` that T42's two local valuations imply
the global valuation \(v_2(\operatorname{num}\Delta_N)=N+4\). T43 proves that
this exact profile, even together with positivity and geometric summability,
does not imply cell recurrence. Thus formalizing the global valuation would be
useful cleanup, but not a route to the target.

## Search protocol and limits

This was a bounded search, not a claim that the entire literature has been
exhausted. The cutoff was 2026-08-12 UTC. Searches prioritized primary sources
from 2025–2026, with older primary sources retained only when needed to pin the
best published irrationality exponent for \(\pi\). The search families were:

- fixed-number digit complexity, factor/subword complexity, disjunctivity,
  and normality of \(\pi\);
- powers of rational numbers modulo one, powers modulo varying moduli, and
  finite digit words of powers;
- S-units, linear forms, exceptionally small fractional parts, and digit
  changes;
- arctangent Taylor partial sums, Machin-like formulas, reduced numerators,
  congruences, and residue distribution;
- 2025–2026 work specific to the digits or irrationality exponent of \(\pi\).

The sources inspected were original arXiv manuscripts or the publisher's
article page/PDF. Search-engine summaries were not used as theorem evidence.
The negative conclusion means “no applicable theorem was located in this
bounded, source-checked search,” not a proof that no such theorem exists.

## Exact T40–T43 frontier

| Label | Artifact | What is established | What is not established |
|---|---|---|---|
| `machine-checked` | [`T40T40MachinLocalForcing.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T40T40MachinLocalForcing.lean) | The sampled forcing is an explicit twelve-term rational window. It is exactly a sum of three positive adjacent pairs at base 5 and three at base 239. Clearing one pair gives \(q^2(r+2)-r\), exactly twice an odd integer for \(q=5,239\). | No archimedean residue estimate, cancellation estimate, density, recurrence, or word occurrence. |
| `machine-checked` | [`T41T41MachinV1Equivalence.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T41T41MachinV1Equivalence.lean) | Canonical V1 is equivalent to recurrence of every \(\pi\)-cylinder cell. Under the explicit source premise `IrrationalityMeasureBelow Real.pi 8`, it is equivalent to recurrence of every rational Machin-code cell. | Neither side of either equivalence is proved. |
| `machine-checked` | [`T42T42MachinTwoAdicForcing.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T42T42MachinTwoAdicForcing.lean) | Each three-positive-pair block at base 5 or 239 has rational two-adic valuation exactly 1; its denominator presentation is odd. The even/odd six-term regroupings are exact. | The combined forcing's global valuation is not formalized, and no archimedean consequence is proved. |
| `machine-checked` | [`T43T43TwoAdicForcingSeparator.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T43T43TwoAdicForcingSeparator.lean) | An artificial positive, geometric, summable forcing has the exact certificate \(2^{N+4}15258789/5^{11(N+1)}\), while its forced orbit converges to \(1/3\) and eventually avoids \([0,1/10)\). | It is not the Machin forcing and makes no direct claim about \(\pi\). |

T38 is important context: the rational Machin orbit is a summably translated
copy of the \(\pi\) orbit at every fixed Fourier frequency. Its forced
recurrence is therefore a coordinate presentation, not an independent source
of randomness. A proof of Weyl cancellation for it would prove the same open
fixed-\(\pi\) cancellation statement.

## Adversarial implication audit

### 1. The global two-adic valuation does follow locally

Status: `proof sketch` (gap-free mathematics, not registered as a Lean theorem).

Let \(A_N\) and \(B_N\) be T42's positive three-pair blocks at bases 5 and
239 after the even/odd regrouping. T40 and T42 give

\[
  \Delta_N=10^{N+1}(16A_N+4B_N),\qquad
  v_2(A_N)=v_2(B_N)=1.
\]

Consequently

\[
  v_2(16A_N)=5,\qquad v_2(4B_N)=3.
\]

The two weighted valuations are unequal, so the non-archimedean equality for
a sum with unequal valuations gives \(v_2(16A_N+4B_N)=3\); there is no possible
two-adic cancellation at this step. Since \(v_2(10^{N+1})=N+1\),

\[
  v_2(\Delta_N)=N+4.
\]

T42's odd-denominator presentations identify this with the exponent of 2 in
the reduced numerator. This confirms the global law already recorded as a
`proof sketch` in [`ultrapi.md`](../../ultrapi.md). It does not advance cell
coverage because T43 satisfies the same law and eventually avoids a cell.

### 2. Positivity and summability do not randomize the orbit

Status: `machine-checked` separator.

T43 directly refutes the implication

\[
  \text{positive + geometric + summable + exact }(N+4)\text{ profile}
  \Longrightarrow \text{one-cell recurrence}.
\]

More conceptually, a summable coboundary can translate an orbit toward a
periodic rational seed. It supplies no entropy and no independent sampling.
This is also why a new, faster Machin-like approximation by itself would not
help.

### 3. Local \(p\)-adic information does not select an archimedean cell

Status: `proof sketch` obstruction.

The V1 target asks where a reduced rational residue lies in the ordered
interval \([a/10^m,(a+1)/10^m)\). A valuation constrains divisibility of its
numerator or denominator, but not the least residue's archimedean location.
Chinese-remainder data at finitely many primes similarly leaves many possible
ordered residues. T43 realizes this separation exactly for the two-adic
profile; the nested-grid separator already recorded in `ultrapi.md` realizes
the same issue with substantially more moving-modulus data at `proof sketch`
status.

### 4. Complexity lower bounds are orders of magnitude too weak

Status: `literature-checked`.

For a decimal word to be disjunctive one needs
\(p_\pi(m)=10^m\) for every \(m\). Irrationality alone gives the
Morse–Hedlund floor \(p_\pi(m)\ge m+1\). The recent results below improve
linear constants or prove superlinearity for other algebraic orbits. Neither
linear nor superlinear complexity implies that a prescribed word occurs, and
it is exponentially below \(10^m\).

### 5. The known irrationality exponent of \(\pi\) enables transfer, not coverage

Status: `literature-checked` external input.

Zeilberger–Zudilin prove \(\mu(\pi)\le 7.103205334137\ldots<8\). This is the
published premise represented explicitly in the T36–T41 chain. It supports the
informal specialization of T41's equivalence to the actual \(\pi\), but gives
no all-cell recurrence. The 2025–2026 complexity theorems requiring
\(\mu<2.324\ldots\), or exactly \(\mu=2\), cannot currently be instantiated for
\(\pi\).

### 6. No hidden implication was found

Status: `literature-checked` adversarial verdict.

After checking signs, weights, quantifiers, and the distinction between
archimedean and non-archimedean information, the frontier is:

\[
\text{exact rational recurrence and local arithmetic}
\quad\not\Rightarrow\quad
\text{any prescribed missing cell is recurrent}.
\]

The still-special data are the exact twelve-term numerator formula and the
one selected moving-modulus residue. A new theorem would have to act on that
deterministic, nonautonomous object rather than on an average over residues.

## 2025–2026 primary-source audit

### Fixed-number digit complexity

1. **Bugeaud–Kaneko–Kim, “On the irrationality exponent of real numbers with
   low complexity expansion,” arXiv:2510.17177v3 (20 Mar 2026).**
   [Primary source](https://arxiv.org/abs/2510.17177)

   Status: `literature-checked`.

   Theorem 1.3 proves that if \(\mu(\xi)=2\), then
   \(\limsup p(n,\xi,b)/n\ge4/3\); its \(\mu>2\) formula is nontrivial only
   for \(\mu<2.2\). The exact irrationality exponent of \(\pi\) is unknown,
   and even the \(\mu=2\) conclusion is only linear. It does not imply one
   prescribed word, disjunctivity, or normality.

2. **Bugeaud–Kim, “On the \(b\)-ary expansion of a real number whose
   irrationality exponent is close to 2,” arXiv:2510.02059v2 (20 Apr 2026).**
   [Primary source](https://arxiv.org/abs/2510.02059)

   Status: `literature-checked`.

   Theorem 1.4 gives nontrivial linear lower bounds only for
   \(\mu<2.246\ldots\) (liminf) or \(\mu<2.324\ldots\) (limsup). The paper
   itself records \(\mu(\pi)\le7.10321\) as the best known bound and says the
   exact value remains unknown. Therefore the theorem does not currently
   apply to \(\pi\), and its conclusion would still be exponentially short
   of V1.

3. **Razeto–Rossi, “Can \(\pi\) generate itself? A Monte Carlo analysis of
   314 trillion digits,” arXiv:2608.06438v1 (6 Aug 2026).**
   [Primary source](https://arxiv.org/abs/2608.06438)

   Status: `experiment`.

   The manuscript explicitly says the Monte Carlo analysis is not a proof of
   normality and that no proof is known for \(\pi\). It is finite statistical
   evidence only and cannot prove a future occurrence.

4. **Roba–Podnieks, “Digits of pi: limits to the seeming randomness II,”
   arXiv:2504.10394v1 (14 Apr 2025).**
   [Primary source](https://arxiv.org/abs/2504.10394)

   Status: `experiment`.

   This is a statistical analysis of finite digit prefixes (ten billion
   digits for \(\pi\)). Its own discussion distinguishes finite testing from
   theorem proving. It supplies no digit-occurrence theorem.

### Rational powers, changing moduli, and complexity

5. **Stephan, “Superlinear complexity of the \((3/2)^n\) steering word,”
   arXiv:2607.11648v3 (3 Aug 2026).**
   [Primary source](https://arxiv.org/abs/2607.11648)

   Status: `literature-checked`.

   The main theorem is \(p_T(k)/k\to\infty\) for the autonomous nearest-
   integer steering itinerary of \((3/2)^n\). The paper explicitly notes that
   density of \((3/2)^n\bmod1\) remains open and that its theorem transfers
   nothing back to density. Its key repeated-factor identity is
   position-uniform because the dynamics is autonomous, and its Diophantine
   variables lie in the fixed group \(\langle2,3\rangle\).

   The Machin recurrence is nonautonomous: the forcing changes with \(N\),
   and its term denominators contain the moving factors
   \(12N+c\). Equal digit blocks do not compress to Stephan's fixed-group
   identity. No direct specialization or fixed-\(\Gamma\) recoding was found.
   Even if it transferred, superlinearity would not imply full cell coverage.

6. **Stephan, “Aperiodicity and subword complexity in the binary expansion
   of powers of three,” arXiv:2607.14774v2 (3 Aug 2026).**
   [Primary source](https://arxiv.org/abs/2607.14774)

   Status: `literature-checked`.

   Theorem A gives \(\Omega(\log m/\log\log m)\) breaks of every fixed period
   in the finite binary word for \(3^m\). Theorem B gives only the finite
   Morse–Hedlund floor \(p_{3^m}(n)\ge n+1\) for fixed \(n\) and sufficiently
   large \(m\). These are effective Baker–Wüstholz consequences for powers of
   one algebraic integer, not a theorem about \(\pi\), changing composite
   moduli, or prescribed-word coverage.

7. **Meng–Dang, “Distribution of powers modulo \(p\) and security of RSA,”
   Journal of Mathematical Cryptology 20 (2026), article 20250020, published
   4 May 2026.**
   [Publisher/DOI source](https://doi.org/10.1515/jmc-2025-0020)

   Status: `literature-checked`.

   Theorem 1 averages over every \(m\in\mathbb F_p^*\) at one prime \(p\) and
   estimates the displacement of the permutation \(m\mapsto m^a\), assuming
   \(\gcd(a,p-1)=1\). It does not treat a single selected orbit value, a
   composite modulus, or a modulus that changes at every index. Its complete-
   sum averaging variable is absent from the Machin recurrence.

### S-units and linear forms

8. **Nair–Kumar–Rout, “Algebraic approximations to linear combinations of
   S-units,” arXiv:2506.02898v3 (18 Nov 2025).**
   [Primary source](https://arxiv.org/abs/2506.02898)

   Status: `literature-checked`.

   Theorem 1.1 is a finiteness theorem for exceptionally small near-integer
   linear combinations \(\sum_i\alpha_i q u_i\), with \(u_i\) in one fixed
   finitely generated algebraic multiplicative group, a common integer
   multiplier \(q\), a strong height-dependent error bound, Galois
   stability, and a non-pseudo-Pisot condition. It is not an equidistribution
   or interval-hitting theorem.

   The Machin terms have different moving factors \((12N+c)^{-1}\). A single
   common integer multiplier can clear them, but the resulting differing
   quotients are not fixed algebraic coefficients and introduce primes not
   confined to a fixed multiplicative group. No direct instantiation meeting
   all hypotheses was found. More decisively, exceptional *too-close*
   finiteness would not imply visits to every positive-width interval.

   Caution: Stephan's arXiv:2607.11648v3 reports an explicit infinite
   counterexample to Theorem 1.3(i) of this manuscript as printed, caused by
   an omitted strict-positivity hypothesis, and uses a repaired statement.
   The printed Theorem 1.3(i) should not be imported without checking that
   repair. This report does not rely on it.

### Arctangent and Machin formulas

9. **Farhi, “On refinements of two-term Machin-like formulas,”
   arXiv:2601.10300v1 (15 Jan 2026).**
   [Primary source](https://arxiv.org/abs/2601.10300)

   Status: `literature-checked`.

   The paper constructs derived two-term Machin-like identities through
   continued fractions and proves geometric convergence of associated
   rational approximations to \(\pi/4\). It contains no theorem on reduced
   numerator residues of the Taylor partial sums at \(1/5\) or \(1/239\), no
   changing-modulus distribution result, and no digit-occurrence theorem.

Targeted 2025–2026 searches for the reduced numerators or archimedean
residues of the exact Machin Taylor windows found formula-construction and
computation papers, but no primary theorem that applies to (11w) in
`ultrapi.md`. This negative finding is bounded by the protocol above.

### The pinned \(\pi\) irrationality input

10. **Zeilberger–Zudilin, “The Irrationality Measure of \(\pi\) Is at Most
    7.103205334137...,” Moscow Journal of Combinatorics and Number Theory 9
    (2020), 407–419.**
    [Primary source](https://doi.org/10.2140/moscow.2020.9.407)

    Status: `literature-checked` external input.

    This proves a bound below 8 and justifies the source premise used in the
    T36–T41 transfer chain. The retained repository source is
    `zeilberger-zudilin-moscow-2020-9-407.pdf`, SHA-256
    `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`.
    It does not prove \(\mu(\pi)<2.324\), \(\mu(\pi)=2\), or any digit
    distribution statement.

## mathlib applicability audit

Status: `literature-checked` local-library audit.

The inspected mathlib checkout was commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, tag `v4.30.0`.

Useful infrastructure exists:

- `Mathlib/Dynamics/SymbolicDynamics/Basic.lean` defines shifts, cylinders,
  finite patterns, occurrences, languages, and subshifts;
- `Mathlib/Analysis/Fourier/ZMod.lean` and related finite Fourier files can
  express complete finite sums;
- `Mathlib/Analysis/SpecialFunctions/Complex/Arctan.lean` contains
  `Complex.hasSum_arctan` and `Real.hasSum_arctan`;
- `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean` contains the rational
  valuation algebra used by T42, including multiplication and unequal-
  valuation sum tools;
- `Mathlib/RingTheory/DedekindDomain/SInteger.lean` defines S-integers and
  S-units.

No domain theorem for disjunctive expansions, normal numbers, factor/subword
complexity of a fixed number, Baker–Wüstholz, the Subspace Theorem, an
S-unit approximation theorem, or distribution of one power sequence modulo
changing moduli was found. In particular, `SInteger.lean` explicitly lists
finite generation and Dirichlet's S-unit theorem as TODOs; it is structural
infrastructure, not the Nair–Kumar–Rout or Evertse–Schlickewei input.
`Nat.ModEq.pow_totient` supplies only elementary fixed-modulus periodicity.

Thus mathlib can support formalization of the global T42 valuation and the
statement of a future archimedean theorem, but it contains no existing bridge
from the present arithmetic to V1.

## What would constitute a breakthrough

The remaining target is not another local valuation. A material next theorem
would have to establish one of the following for the *actual* Machin residue
sequence:

1. for every \(m,a\), infinitely many \(N\) place the exact reduced residue
   in \([a/10^m,(a+1)/10^m)\); or
2. a cancellation estimate for every nonzero fixed Fourier frequency,
   strong enough for Weyl equidistribution (stronger than V1); or
3. a new deterministic changing-composite-modulus theorem that applies to
   the exact twelve-term numerator formula, not to an average over all
   residues and not merely to its local valuations.

The \((3/2)^n\) steering-word work suggests a possible *method question*:
can equality of two Machin digit blocks be compressed into a fixed-group
S-unit inequality with all moving linear denominators eliminated? At present
this is a `conjecture` about a possible reduction, not a theorem. The exact
nonautonomous forcing is the obstruction, and no such compression was found.

## Source pins

The following SHA-256 values were computed from the PDFs fetched on
2026-08-12 UTC. The version suffixes are the versions inspected.

| Source | PDF SHA-256 |
|---|---|
| arXiv:2510.17177v3 | `c825aac435e48f4668d8d1a496869c8c1e86ff1d18cea407e2c0156ece1bdd01` |
| arXiv:2510.02059v2 | `fd557275332e2a360aaf6ef55a651746fd0b271b009e1df48f5f970991723330` |
| arXiv:2607.11648v3 | `8ed933403a1843d864a269482d0a505050704c7de72a2448b3224b42b09734ee` |
| arXiv:2607.14774v2 | `48ed1f05908ae4c1da7046c45b85cb09674e8af5b0c60dd90939638cee283e92` |
| arXiv:2506.02898v3 | `9b865547c1de290426b13086abe4fcaf5394e79537fbcad56205bd4546a6904a` |
| arXiv:2601.10300v1 | `86cdd17355a4462db9ac18b6e7dcfe2559e14089ed02272247df6cd71ce7b90e` |
| arXiv:2608.06438v1 | `4418a1b83f91470dfd57ebcecd0d882a32fc1a6f2cb14661be45a7bf55d551be` |
| arXiv:2504.10394v1 | `616e9e0d185de2db7252131091100940f4971d32c9acd0f8b57fcff1c935f3e0` |
| arXiv:1912.06345v2 | `b922ee68a427ad5b74617bd2ac6b6a549824eb2d5a8c97eed0d34b2de984155f` |

## Final status

- Every finite decimal word in \(\pi\): `conjecture`.
- Exact T40–T43 statements listed above: `machine-checked`.
- Global \(N+4\) valuation derived from T42: `proof sketch`, already present
  in `ultrapi.md`, not sufficient for recurrence.
- This dated primary-source and mathlib audit: `literature-checked`.
- Complete proof of V1: not obtained.

## T44 independent formal review — 2026-08-12 UTC

Review status: `machine-checked` for the theorem statements and build; the
line-by-line scope assessment below is `literature-checked`. This section is
a later point-in-time update and supersedes only the earlier statement that
the global \(N+4\) valuation was still a `proof sketch`.

Reviewed artifact:
[`T44T44MachinTotalTwoAdicForcing.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T44T44MachinTotalTwoAdicForcing.lean),
initial-review SHA-256
`9e1cc422dd35bab7f8163bed3f0b215a669bb2af6e9b6edfbca04b19c4f86136`.
After that review, another workstream added the three explicit reduced-form
bridge declarations discussed below.  The current reviewed SHA-256 is
`47ec25f09c75d133f899aa563b0cddc3284b18319b49dae784738cef40debc8b`.
No edit was made to T44 by this reviewer; the two hashes record the actual
chronology rather than treating the later extension as part of the initial
snapshot.

### Verdict

No correctness, indexing, sign, nonzero-premise, registration, axiom, or
scope defect was found. T44 correctly promotes the previously gap-free
global valuation argument to `machine-checked` status:

\[
  \operatorname{padicValRat}_2(\operatorname{sampledMachinForcingRat}(N))
  =N+4.
\]

The module's closing scope disclaimer is accurate. This theorem is exact
arithmetic information about the actual rational Machin forcing, but T43
shows that this invariant cannot imply a cylinder hit or recurrence.

### Index and sign audit

T40 defines

\[
 \Delta_N=10^{N+1}\bigl(16W_5(6N+2)-4W_{239}(6N+3)\bigr).
\]

For the base-5 window,
\(6N+2=2(3N+1)\). T42's even-window lemma therefore gives a positive
three-pair block beginning at

\[
  4(3N+1)+1=12N+5.
\]

For the base-239 window,
\(6N+3=2(3N+1)+1\). T42's odd-window lemma gives the *negative* of a
three-pair block beginning at

\[
  4(3N+1)+3=12N+7.
\]

The outer coefficient is \(-4\), so these two negative signs cancel. T44's
formula

\[
 \Delta_N=10^{N+1}\bigl(16A_N+4B_N\bigr)
\]

has the correct indices and signs. The `ring` closure does not hide a sign
choice; all four index equalities are explicitly rewritten first.

### Valuation and nonzero audit

T42 applies because

\[
 12N+5=2(6N+2)+1,\qquad 12N+7=2(6N+3)+1,
\]

so both starting exponents are odd. It gives
\(v_2(A_N)=v_2(B_N)=1\). T44 then checks:

- \(v_2(4)=2\) and \(v_2(10)=1\);
- \(A_N\ne0\) and \(B_N\ne0\), since mathlib defines
  `padicValRat 2 0 = 0`, contradicting their valuation 1;
- \(v_2(4A_N)=3\), whereas \(v_2(B_N)=1\);
- \(4A_N+B_N\ne0\), because equality \(4A_N=-B_N\) would force the
  incompatible valuations 3 and 1;
- `padicValRat.add_eq_of_lt` is used in the correct direction after commuting
  the sum: \(v_2(B_N)<v_2(4A_N)\), hence
  \(v_2(B_N+4A_N)=v_2(B_N)=1\);
- factoring \(16A_N+4B_N=4(4A_N+B_N)\) gives valuation \(2+1=3\);
- the weighted block sum is nonzero because its proved valuation is 3, and
  the power \(10^{N+1}\) is nonzero;
- multiplication and power valuation laws finally give
  \((N+1)\cdot1+3=N+4\).

Every nonzero argument required by `padicValRat.mul`,
`padicValRat.pow`, and `padicValRat.add_eq_of_lt` is supplied explicitly.

### Reduced-numerator meaning

In the initial reviewed snapshot, the literal Lean conclusion was a rational
valuation equality rather than a separate theorem mentioning `Rat.num`.  The
docstring's equivalence with “the reduced numerator contains exactly \(N+4\)
factors of two” was nevertheless correct.

Mathlib defines

\[
 v_2(q)=v_2(q.\mathrm{num})-v_2(q.\mathrm{den}),
\]

where `Rat.num` and `Rat.den` are reduced and coprime. Since \(N+4>0\), a
reduced denominator cannot contain a factor of 2: if it did, coprimality
would make the numerator odd and the rational valuation negative. Hence the
reduced denominator is odd and the numerator has valuation exactly \(N+4\).

There is also a direct presentation-level check: T42 writes every pair over
`pairDenominatorNat q r`, which is odd for the odd bases and odd exponents
used here. Finite sums and multiplication by 4, 16, and \(10^{N+1}\) preserve
the existence of an odd common denominator; reduction preserves oddness.
Thus no denominator cancellation can alter the claimed numerator exponent.

That former API gap has now been closed in the current snapshot.  The generic
lemma `odd_den_of_pos_padicValRat_two` proves that positive two-adic rational
order forces an odd reduced denominator: if 2 divided the denominator,
reducedness would force the numerator to be odd, so `padicValRat_def` would
make the rational order negative.  The two specializations
`sampledMachinForcingRat_den_odd` and
`padicValInt_two_sampledMachinForcingRat_num` then state the odd denominator
and the exact reduced-numerator exponent literally.  Their hypotheses,
integer casts, and use of reducedness were checked line by line; no defect was
found.

### Registration, axioms, and verification

- `TheoryLib.lean` imports T44 once, immediately after T43.
- `audit/AxiomAudit.lean` imports T44 once and prints all eight current T44
  declarations: the original five plus the generic odd-denominator bridge,
  its forcing specialization, and the exact reduced-numerator theorem.
- No `sorry`, `admit`, new `axiom`, `unsafe`, `opaque`, or `native_decide`
  declaration occurs in T44.
- Direct compilation of the current T44 snapshot and of
  `audit/AxiomAudit.lean` succeeded on 2026-08-12 UTC.
- Every current T44 `#print axioms` result was exactly
  `[propext, Classical.choice, Quot.sound]`, within the existing allowlist.
- Before the three bridge additions, `scripts/check.ps1` completed
  successfully on the initial snapshot: **8,493 jobs**, followed by
  `PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.`
  The direct current-snapshot checks above cover the new declarations; this
  review does not silently attribute the earlier full-gate run to the later
  hash.

As an independent `experiment`, exact rational recomputation for
\(0\le N\le7\) confirmed the T40/T44 block identity, an odd reduced
denominator, and reduced-numerator valuations \(4,5,\ldots,11\), respectively.
This finite check is only corroboration; the Lean theorem proves all \(N\).

### Updated frontier status

- Total rational forcing valuation \(N+4\): `machine-checked` by T44.
- Odd reduced denominator and exact exponent in the reduced numerator:
  separately `machine-checked` and axiom-registered by the three current T44
  bridge declarations.
- Any implication to density, recurrence, normality, or V1: not obtained;
  T43 remains a `machine-checked` separator against that inference.

## Prime-pulse adversarial review — 2026-08-12 UTC

Reviewed artifact:
[`machin_recurrence_report.md`](machin_recurrence_report.md), SHA-256
`e49cd58db36a72a09dfe216fd7695d9da072f4295318daf7b333bb8cbecb41a1`.
The arithmetic below is an independent review of that snapshot.  Statements
explicitly labelled `proof sketch` have not been promoted to the verified
Lean track.

### Verdict on Lemmas 2--4 and the exceptional prime

Status: `proof sketch`, with exact-computation corroboration labelled
separately below.

No fatal arithmetic, sign, index, or quantifier defect was found.

- In Lemma 2, each \(U_q(r)\) is a degree-five polynomial, with nonzero
  leading coefficient
  \(q^{10}-q^8+q^6-q^4+q^2-1=(q^{12}-1)/(q^2+1)\).
  Therefore the two degree-six polynomial-exponential components and the
  displayed order-14 annihilator are correct.  Strictly, the argument first
  proves that displayed recurrence polynomial is an *annihilator*; calling
  it the characteristic polynomial should not be read as a separate
  minimality theorem.
- In Lemma 3, the two terms sharing
  \(p=12N+5+2k\) have combined residue proportional to
  \(4(-1)^k(4\cdot239-5)=4(-1)^k951\).  Since
  \(951=3\cdot317\), \(p>12\), and the eligible slots
  \(k=1,3,4\) put \(p\) in the classes \(7,11,1\pmod {12}\), the exceptional
  factor \(317\equiv5\pmod {12}\) cannot occur.  The window has width 12,
  so every other linear denominator is a \(p\)-unit.  Hence the claimed
  valuation \(-1\) follows.
- The separate \(p=239\) treatment is correct.  At \(N=19\), the base-239
  exponents are \(235,237,239,241,243,245\).  Their 239-adic valuations are
  respectively \(-235,-237,-240,-241,-243,-245\); the last is the unique
  minimum.  The base-5 window has valuation at least \(-1\), so it cannot
  cancel that term.
- In Lemma 4, the preceding rational sample is \(p\)-integral, the future
  forcing is \(p\)-integral while \(12n+17<3p\), and multiplying the recurrence
  by \(p\) really does propagate the residue by 10.  Solving this inequality
  gives \(0\le t\le2N\) for \(k=1\) and
  \(0\le t\le2N+1\) for \(k=3,4\), exactly as stated.

As an `experiment`, independent exact rational calculations rechecked all
four items for finite ranges.  This is useful error detection, not proof.

### Corrected complementary-phase analysis

Status: `proof sketch`, derived directly from the exact T38 identities.

The report's first CRT decomposition is algebraically correct, but its
description of the complementary factor as an arbitrary changing weight is
too pessimistic.  Let

\[
 y_n=10^nM_{3n},\qquad s_n=10^n(\pi-M_{3n}),\qquad
 \rho=\frac{10}{625^3}=\frac{10}{5^{12}}.
\]

T38 gives, exactly,

\[
 y_{n+1}=10y_n+\Delta_n,qquad
 \Delta_n=10s_n-s_{n+1},qquad 0\le s_n<\rho^n.
\]

Iteration and telescoping therefore give, for every \(t\ge0\),

\[
 y_{n+t}=10^t y_n+R_{n,t},\qquad
 R_{n,t}=\sum_{j=0}^{t-1}10^{t-1-j}\Delta_{n+j}
          =10^ts_n-s_{n+t}.                 \tag{P1}
\]

Consequently

\[
 |R_{n,t}|<10^t\rho^n+\rho^{n+t}.           \tag{P2}
\]

If the pulse starts at \(n=N+1\) and
\(y_n=a_0/(pD_0)\) in lowest terms, with
\(A_0\equiv a_0D_0^{-1}\pmod p\), choose \(E_0\pmod {D_0}\) so that
\(a_0/(pD_0)\equiv A_0/p+E_0/D_0\pmod1\).  Then the *entire* pulse phase is

\[
 e(hy_{n+t})
 =e_{pD_0}(ha_0\,10^t)e(hR_{n,t})
 =e_p(hA_0\,10^t)e_{D_0}(hE_0\,10^t)e(hR_{n,t}). \tag{P3}
\]

Thus there is fixed initial modulus \(pD_0\), not an unconstrained sequence
of moduli and weights, plus an exponentially small archimedean perturbation.
For the full pulse \(t\le2N+1\), the first term in (P2) is at most
\(10^{2N+1}\rho^{N+1}\), which decays exponentially because
\(100\rho=1000/5^{12}<1\).  This is genuine route leverage and should replace
the arbitrary-weight formulation of equations (23)--(26) in the reviewed
snapshot.

It is not yet a cancellation theorem.  It replaces the missing estimate by
the very specific ultra-short sum

\[
 \sum_{t<T}e_{pD_0}(ha_0\,10^t),\qquad
 T\asymp N\asymp\log(pD_0), \tag{P4}
\]

plus a negligible error.

### Why existing exponential-sum results still do not close (P4)

Status: `literature-checked` on 2026-08-12 UTC.

The primary sources closest to (P4) were checked at theorem level.

1. **Kerr, “Incomplete exponential sums over exponential functions,”
   arXiv:1302.4170 (2013).**
   [Primary source](https://arxiv.org/abs/1302.4170)

   Kerr treats
   \(S_{g,p}(\lambda,T)=\sum_{t\le T}e_p(\lambda g^t)\) for a *prime* modulus
   and \(g\in\mathbb F_p^*\).  Theorem 2 is nontrivial only in polynomial
   ranges depending on \(p\) and the multiplicative order; its displayed
   bounds contain positive powers such as \(p^{1/8}\).  It gives no saving
   for \(T\asymp\log p\), and it does not include the Machin cofactor.

2. **Bourgain--Chang, “Exponential sum estimates over subgroups and almost
   subgroups of \(\mathbb Z_q^*\), where \(q\) is composite with few prime
   factors,” GAFA 16 (2006), 327--366.**
   [Author-hosted primary source](https://math.ucr.edu/~mcc/paper/122%20NewExp.pdf)

   Corollary 4.5 does treat incomplete geometric sums modulo a composite
   \(q\), but assumes the base is in \(\mathbb Z_q^*\), requires
   \(T>q^\delta\), and requires its order modulo every prime divisor of \(q\)
   to exceed \(q^\delta\).  The Machin pulse has \(T\asymp\log q\), while
   \(10\) is not a unit at the large 5-primary divisor.  None of these three
   hypotheses is a cosmetic mismatch.  The paper itself gives a
   prime-square example where an incomplete sum is asymptotic to its full
   length despite a large total order.

3. **Bailey--Crandall, “Random Generators and Normal Numbers” (2003).**
   [Primary source](https://www.davidhbailey.com/dhbpapers/bcnormal.pdf)

   Their Lemma 4.5 records the Korobov--Niederreiter composite-modulus bound
   only for \((b,c)=1\).  The resulting discrepancy theorem has a
   square-root-modulus term, so it becomes useful for orbit blocks of order
   at least roughly \(c^{1/2}\), not logarithmic blocks.  Their concluding
   open problem explicitly asks for a generalization beyond the coprime
   setting.

4. **Di Benedetto--Garaev--García--González-Sánchez--Shparlinski--Trujillo,
   “New estimates for exponential sums over multiplicative subgroups and
   intervals in prime fields,” arXiv:2003.06165 (2020).**
   [Primary source](https://arxiv.org/abs/2003.06165)

   Its subgroup cancellation starts at subgroup size \(>p^{1/4}\); its
   interval/subgroup double sums also require polynomial-size sets.  It does
   not provide arbitrary weights equal to the exact Machin cofactor residues,
   nor a logarithmic-length result.

No searched primary theorem treats the exact cofactor weight in (P3), a
nonunit base on the 5-primary part, and \(T\asymp\log q\).  This negative
finding is bounded by the listed search, not a claim that no such theorem can
exist.

Write \(pD_0=5^sQ\), with \((5,Q)=1\).  CRT does isolate the odd coprime
component:

\[
 e_{pD_0}(a_0 10^t)=e_{5^s}(u\,10^t)e_Q(v\,10^t).
\]

The first factor becomes identically 1 only when \(t\ge s\), because then
\(5^s\mid10^t\).  The pulse ends near \(2N\).  Exact reduced-denominator
calculation for all 263 eligible pulses with \(N\le199\) found \(s>2N+2\),
indeed a minimum observed ratio \(s/(2N+2)>5.50\).  This is an `experiment`,
not a global lower bound.  Proving a uniform 5-adic denominator lower bound
for \(y_{N+1}\) is now a precise arithmetic obligation if this split is to be
used rigorously.

### Conditional CRT-mesh separator at logarithmic scale

Status: `proof sketch`; the application to every Machin pulse is conditional
on an unproved lower bound for its reduced 5-primary denominator.

There is a simple rigorous reason why merely retaining the fixed prime pulse
cannot select the real cylinder.  Let

\[
 q=p\,5^sD^*,\qquad (p,5D^*)=1,\qquad s\ge1,
\]

and fix a nonzero desired \(p\)-component \(A\).  Choose \(a_*\) satisfying

\[
 a_*\equiv A(5^sD^*)\pmod p,\qquad a_*\equiv1\pmod {D^*}.
\]

Such a solution exists by CRT.  Vary

\[
 a_j=a_*+pD^*j\qquad (j\bmod5^s).
\]

The fractions \(a_j/q\pmod1\) are a shifted grid of mesh \(5^{-s}\), all
with the same \(p\)-component.  Exactly one class of \(j\pmod5\) makes the
numerator divisible by 5.  After deleting that class, consecutive surviving
points have cyclic gaps at most \(2/5^s\); the remaining congruences make
each numerator coprime to \(pD^*\), so the survivors have reduced denominator
exactly \(q\).  Therefore, if

\[
 \frac{2}{5^s}<10^{-L},                         \tag{P5}
\]

every length-\(L\) decimal cylinder contains a reduced seed with that exact
denominator and the prescribed \(p\)-component.  Multiplication by \(10^t\)
then preserves \(p\)-adic valuation \(-1\) and the geometric \(p\)-residue for
\(0\le t<L\), yet the chosen cylinder prescribes the whole first
\(L\)-digit orbit segment.  For example, choosing the word \(55\ldots5\)
puts each of those iterates in \([0.5,0.6)\), avoiding \([0,0.1)\).

Because (P5) is strict, the seed can be chosen in a smaller concentric
subinterval with some positive guard \(g\) from the cylinder boundary.  The
exact perturbation (P2) can be added whenever
\(\max_{t<L}|R_{n,t}|<g\).  Thus (P5), together with a suitable
Machin 5-adic lower bound, would be a clean separator: the complete prime
residue pulse and fixed-denominator structure do not by themselves force a
cell hit.  The actual numerator/cofactor correlation remains indispensable.

The construction varies the numerator; it does not preserve the actual
Machin numerator or its full cofactor residue.  It therefore separates only
arguments based on the prime pulse plus fixed denominator.  It does **not**
refute a route using the actual Machin numerator; it identifies exactly what
such a route must exploit.

### T45 point-in-time review

Reviewed artifact:
[`T45T45MachinPrimeSurvival.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T45T45MachinPrimeSurvival.lean),
SHA-256
`92f773c26b348a283fb139a94d96e48ac2804af861b8013cbca6069e1584fff0`.

Status: the file's statements compile in Lean, and its five printed main
declarations depend only on `[propext, Classical.choice, Quot.sound]`.
The line-by-line mathematical review found no objection: the signs and
indices match the preceding audit, Fermat reduction to 951 is correct, the
regular-term proof uses the strict width correctly, and the unequal-valuation
sum argument establishes the final (-1).

At this snapshot, however, T45 was not imported by `TheoryLib.lean` or
`audit/AxiomAudit.lean`.  Under this repository's workflow it therefore
should not yet be reported as an axiom-audited `machine-checked` research
claim.  This is an integration/registration issue, not a mathematical flaw,
and this review made no Lean-file edit.

Point-in-time integration update: after that standalone snapshot,
`TheoryLib.lean` imported T45, `audit/AxiomAudit.lean` registered all 31 of
its declarations, and the full **8,493-job** verification gate passed.  The
prime-survival theorem may therefore now be labelled `machine-checked`; this
chronological update does not alter the proof-sketch status of the later
pulse and CRT arguments.

### Revised frontier

- Lemmas 2--4 and the (p=239) case: no fatal flaw found; `proof sketch` in
  the reviewed report.
- T45 prime-survival theorem: `machine-checked` after the later import,
  31-declaration axiom registration, and full verification-gate pass.
- Complementary phase: exactly reducible to one fixed initial modulus plus a
  uniformly tiny telescoping error; this is real route leverage.
- Known exponential-sum bounds: still inapplicable at logarithmic length and
  with the 5-primary nonunit component; `literature-checked`.
- Complete proof that every finite decimal word occurs in \(\pi\): still a
  `conjecture`; no complete proof or candidate resolution is claimed.
