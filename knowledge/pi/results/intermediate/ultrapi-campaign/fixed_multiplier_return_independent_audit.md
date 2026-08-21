# Independent audit: fixed-multiplier return attack

Audit date: **2026-08-12 UTC**
Target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt)
Target SHA-256:
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Verdict

**PASS after three scoped corrections.**

The central Ramanujan obstruction is a valid proof sketch.  Its exact
two-adic calculation, reduced-denominator lower bound, tail lower bound, and
denominator/error contradiction all rederive cleanly.  The Wallis
denominator/error obstruction is also valid.  The source applicability
claims for Ramanujan, Furstenberg, BBP, Yu, Sondow--Yi, Holcombe, AGM, and
Chudnovsky are appropriately limited.

The original draft did not prove its attractive all-depth BBP valuation
formula: its checker tested only sixty cases.  That statement has been
downgraded to experiment, and a rigorous even-depth theorem has replaced it
where a theorem is needed.  Two endpoint wordings were also tightened:
Wallis's prime assertion now assumes \(K\ge2\), and Viète irrationality now
starts at the nontrivial depth \(h\ge1\).

No fixed-multiplier return or V1 proof was found.  Canonical V1 remains a
conjecture.  The audited negative results remain proof sketch, the finite
replays remain experiment, and the dated source audit remains
literature-checked.  Nothing is a candidate resolution.

## 1. Artifacts and correction record

Audited branch artifacts:

- [fixed_multiplier_return_attack.md](fixed_multiplier_return_attack.md)
- [fixed_multiplier_return_check.py](fixed_multiplier_return_check.py)

Independent replay:

- [fixed_multiplier_return_independent_check.py](fixed_multiplier_return_independent_check.py)

Point-in-time pre-audit hashes were

    e7cb802d71c5685f6cde17e998e65b93952e5bd6a2f46b66f7cc548a523b1c53  fixed_multiplier_return_attack.md
    0a551a937ca1cec4f7e81445779e19add5bec6dbc461f704743370f1ca02cd80  fixed_multiplier_return_check.py

The checker itself needed no correction.  The report was amended as follows.

1. “Every prime \(K<p\le2K\)” was false at the irrelevant endpoint \(K=1\),
   where \(p=2\).  It now says \(K\ge2\), making every such prime odd.
2. The claimed all-\(N\) BBP formula
   \(v_2(\operatorname{den}B_N)=4N-v_2(N+1)\) had only finite evidence and no
   induction or source.  It is now explicitly experiment.  The report adds
   the exact theorem
   \(v_2(\operatorname{den}B_N)=4N\) for every even \(N\).
3. The statement that every finite Viète depth is irrational overlooked
   \(V_0=2\).  It now applies to every nontrivial depth \(h\ge1\).

These corrections narrow ancillary claims but do not alter the exact
Ramanujan or Wallis obstructions.

## 2. Fixed-return normalization

Let \(q_n=10^n-c\), with \(c\ge2\) multiplicatively independent of ten.
The report correctly uses

\[
 c\pi\in K_{10}(\pi)
 \quad\Longleftrightarrow\quad
 \liminf_{n\to\infty}\|q_n\pi\|_{\mathbb T}=0.           \tag{A1}
\]

The nonlacunary-semigroup theorem then makes (A1) equivalent to V1.  The
commutation step is sound: a sequence \(10^{n_j}\pi\to c\pi\) implies
\(cK_{10}(\pi)\subseteq K_{10}(\pi)\), and the dense joint
\(\langle10,c\rangle\)-orbit is contained in that closure.

The rational formulation is also exact.  A return subsequence gives nearest
integers \(m_j\) with

\[
 \left|\pi-\frac{m_j}{q_{n_j}}\right|
 =\frac{\|q_{n_j}\pi\|_{\mathbb T}}{q_{n_j}}
 =o(q_{n_j}^{-1}),                                      \tag{A2}
\]

and conversely (A2) gives (A1).  Thus a rapidly convergent identity matters
only if it also controls the selected residue modulo \(q_n\).

## 3. Independent Wallis derivation

For

\[
 W_K=2\prod_{k=1}^K\frac{4k^2}{4k^2-1},
\]

the exact partial fraction

\[
 \frac1{4k^2-1}
 =\frac12\left(\frac1{2k-1}-\frac1{2k+1}\right)
\]

gives

\[
 \sum_{k>K}\frac1{4k^2-1}=\frac1{4K+2}.                 \tag{A3}
\]

All omitted product factors are positive.  The product minus one strictly
exceeds the linear tail, and \(W_K\ge2\), so

\[
                       \pi-W_K>\frac1{2K+1}.             \tag{A4}
\]

Thus \(q_n(\pi-W_K)\to0\) requires \(K/q_n\to\infty\).

For \(K\ge2\) and prime \(K<p\le2K\), the denominator factors
\(2k-1=p\) and \(2k+1=p\) occur at \(k=(p+1)/2\) and
\(k=(p-1)/2\).  No numerator \(2k\), \(k\le K<p\), contains \(p\), and no
other odd multiple of \(p\) lies in range.  Hence

\[
                         v_p(\operatorname{den}W_K)=2.   \tag{A5}
\]

The prime number theorem yields
\(\log\operatorname{den}W_K\ge(2+o(1))K\).  If that denominator divided
\(q_n<10^n\), then \(K=O(n)\), contradicting the exponentially larger
condition \(K/q_n\to\infty\).  The corrected logic is sound.

## 4. Independent Ramanujan two-adic audit

Ramanujan's equation (29), in the original source's notation, is

\[
 \frac{16}{\pi}
 =5+\frac{47}{64}\left(\frac12\right)^3
  +\frac{89}{64^2}\left(\frac{1\cdot3}{2\cdot4}\right)^3+\cdots .
\]

Since

\[
 \frac{1\cdot3\cdots(2k-1)}{2\cdot4\cdots2k}
 =\frac{\binom{2k}{k}}{4^k},
\]

this is exactly

\[
 \frac{16}{\pi}
 =\sum_{k\ge0}\frac{(42k+5)\binom{2k}{k}^3}{2^{12k}}.   \tag{A6}
\]

Let \(U_N=2^{12N}S_N\).  The coefficient \(42k+5\) is odd, and Kummer's
carry formula gives

\[
 v_2\binom{2k}{k}=s_2(k).                               \tag{A7}
\]

The endpoint \(k=N\) has valuation \(3s_2(N)\).  If \(k=N-d<N\), then
\[
 s_2(N)\le s_2(k)+s_2(d),\qquad s_2(d)\le d,
\]
and therefore
\[
 12d+3s_2(k)
 \ge3s_2(N)+12d-3s_2(d)
 \ge3s_2(N)+9d>3s_2(N).                                \tag{A8}
\]

The endpoint is the unique two-adic minimum, proving

\[
                         v_2(U_N)=3s_2(N).               \tag{A9}
\]

Because \(A_N=16\,2^{12N}/U_N\) and
\(3s_2(N)<12N+4\), reduction cancels exactly the power in (A9):

\[
 \operatorname{den}(A_N)
 =\frac{U_N}{2^{3s_2(N)}}.                              \tag{A10}
\]

Positivity and the \(k=0\) term give
\[
 \operatorname{den}(A_N)
 \ge5\,2^{12N-3s_2(N)}
 \ge\frac{5\,2^{12N}}{(N+1)^3},                         \tag{A11}
\]
where \(2^{s_2(N)}\le N+1\).  Every step is exact.

## 5. Independent Ramanujan error/denominator mismatch

For \(m=N+1\), centrality of \(\binom{2m}{m}\) among the \(2m+1\) binomial
coefficients gives

\[
 \binom{2m}{m}\ge\frac{4^m}{2m+1}.
\]

The first omitted positive term in (A6) therefore yields

\[
 \frac{16}{\pi}-S_N
 \ge\frac{42m+5}{64^m(2m+1)^3}.                         \tag{A12}
\]

Writing \(T=16/\pi\), positivity and \(S_N<T<6\) give

\[
 A_N-\pi
 =\frac{16(T-S_N)}{S_NT}
 >\frac49\,\frac{42m+5}{64^m(2m+1)^3}.                 \tag{A13}
\]

Suppose \(q_nA_N\in\mathbb Z\).  Since (A10) is the reduced denominator,
\(\operatorname{den}(A_N)\mid q_n<10^n\).  Equation (A11) implies

\[
 64^N
 <\frac{10^{n/2}(N+1)^{3/2}}{\sqrt5},\qquad N=O(n).     \tag{A14}
\]

For fixed positive \(c\), eventually \(q_n>10^n/2\).  Inverting (A14) in
(A13) gives

\[
 q_n(A_N-\pi)
 \gg\frac{10^{n/2}}{(N+1)^{7/2}}\longrightarrow\infty.  \tag{A15}
\]

If \(N\) stays bounded, the positive error is fixed and the same conclusion
is immediate.  This exhausts every dependence \(N=N(n)\) under the exact
anchor.  The main negative result is sound.

## 6. BBP correction and exact surviving theorem

For
\[
 B_N=\sum_{k=0}^N16^{-k}
 \frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)},
\]
every coefficient denominator is odd.  When \(N\) is even, its endpoint
numerator is odd.  The endpoint valuation is \(-4N\), whereas all \(k<N\)
terms have valuation at least \(-4N+4\).  The minimum is unique, so
\[
                 v_2(\operatorname{den}B_N)=4N
                 \qquad(N\ {\rm even}).                 \tag{A16}
\]

For fixed nonzero \(c\), once \(n>v_2(c)\),
\[
                         v_2(10^n-c)=v_2(c).             \tag{A17}
\]
Equations (A16)--(A17) exclude exact divisibility along growing even depths.

The stronger pattern
\[
 v_2(\operatorname{den}B_N)=4N-v_2(N+1)                \tag{A18}
\]
passes independent exact computation through \(N=400\), and an additional
diagnostic reached \(N=1500\), but finite evidence is not a proof.  The
correction appropriately leaves odd-only anchor sequences unresolved.  This
does not affect the Ramanujan theorem or the fact that controlling the
transferable \(c=16\) BBP residue would be equivalent to the fixed-pi return.

## 7. Remaining source applicability

The primary-source checks support the corrected, bounded claims.

- Furstenberg's Theorem IV.1 supplies the nonlacunary joint-orbit theorem,
  not the fixed return.
- The original Ramanujan page displays the \(16/\pi\) series at equation
  (29); the conversion to (A6) is exact.
- The BBP paper supplies the base-16 series and digit-extraction algorithm,
  not the unproved all-depth valuation (A18) or decimal return.
- Yu's Theorem 1 bounds
  \(\operatorname{ord}_p(\alpha_1^{b_1}\cdots\alpha_r^{b_r}-1)\) by a
  constant times \(\log B\) for fixed algebraic inputs.  Taking
  \(\alpha_1=10,\alpha_2=c,b_1=n,b_2=-1\), with \(p\nmid10c\) and
  \(10^n\ne c\), gives
  \(v_p(10^n-c)=O_{p,c}(\log n)\).  It gives no simultaneous CRT ordering.
- Sondow--Yi distinguish gamma-derived Wallis products for pi-related
  constants from Catalan-type products for powers of \(e\).
- Holcombe's 2026 abstract includes exponential counterterms, Euler's
  constant, gamma moments, zeta values, and a \(\pi/e^{3/2}\) product.
  These are not rational \(q_n\)-anchors.
- Milla proves the Chudnovsky formula.  Solving a finite truncation for pi
  leaves a rational multiple of \(\sqrt{10005}\), so the algebraic phase
  warning is accurate.

No checked source supplies \(c\pi\in K_{10}(\pi)\) or a selected-residue
estimate that would imply it.  This is a bounded applicability finding, not
a novelty claim.

## 8. Independent replay

The independent script uses no code from the branch checker.  It verifies
Wallis private primes and telescoping, Kummer's valuation, the unique
Ramanujan minimum layer, exact reduced denominators and tail lower bounds,
the BBP pattern through 400 as experiment, the rigorous even-depth BBP
minimum, and fixed-\(c\) primary valuations.

Its clean output is:

    claim_status=experiment
    source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
    wallis_private_prime_exact_checks=1235
    wallis_telescoping_exact_checks=327
    central_binomial_two_adic_exact_checks=151
    ramanujan_unique_minimum_exact_checks=453
    ramanujan_reduced_denominator_exact_checks=453
    ramanujan_tail_lower_exact_checks=302
    bbp_all_depth_observed_checks=400
    bbp_even_depth_proved_pattern_checks=800
    fixed_c_primary_valuation_exact_checks=144
    all exact assertions passed

## Sharp independent conclusion

After correction, the branch establishes two useful method-specific
separators.

1. Wallis cannot simultaneously have transferable error and a reduced
   denominator dividing \(10^n-c\).
2. Ramanujan's rational fast series has exact denominator scale \(4096^N\)
   against error scale \(64^{-N}\); exact anchoring forces the transferred
   error to diverge.

The other product families pay only the approximation entry of the return
ledger or retain a selected numerator phase.  BBP has a proved even-depth
primary obstruction, while its stronger all-depth valuation remains
experiment.  No audited result supplies the return, a cylinder hit, or V1.
