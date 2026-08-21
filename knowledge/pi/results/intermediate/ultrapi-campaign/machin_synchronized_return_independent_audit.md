# Independent audit: synchronized Machin returns

Audit date: **2026-08-12 UTC**  
Audited report:
[`machin_synchronized_return_attack.md`](machin_synchronized_return_attack.md)  
Corrected report SHA-256:
`a99a88cd4435c5361c652c54780a5525c63ef0d5039ccf82cff30a16b748f645`  
Primary checker SHA-256:
`d4c992ef4e4cc3ffee6874004bd56965ad3f4bd88332eca07bdc38273daa4a34`  
Independent checker:
[`machin_synchronized_return_independent_check.py`](machin_synchronized_return_independent_check.py)  
Independent checker SHA-256:
`b423b4dbf9663a4ae9373da3091913b0f00ff1865fc13ba56f5a756dbb061bfc`

Canonical target:
[`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Canonical target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Verdict and claim status

**PASS after three scoped prose/notation corrections.**  The exact
synchronization equivalence, bounded 2/5-primary capacity, natural-common-
denominator error barrier, and private-prime reduced-denominator barrier all
rederive.  The corrected report is a sound `proof sketch` of those scoped
claims.  Its computations independently replay as `experiment`, and its
bounded source applicability check is `literature-checked` as of the audit
date.

The report does not prove V1.  Canonical V1 remains a `conjecture`; this audit
is not a `candidate resolution`.  In particular, the result excludes the
four fixed positive Machin identities and the stated synchronization
mechanisms.  It does not exclude a depth-varying signed identity with
exceptional simultaneous Archimedean and denominator cancellation.

## 1. Exact return criterion rederived

Fix an integer \(c\ge2\) multiplicatively independent of 10 and put

\[
 Q_N=10^N-c.
\]

For large \(N\), \(Q_N>0\).  Suppose \(N_j\to\infty\),
\(A_j\in\mathbb Q\),

\[
 Q_{N_j}A_j\in\mathbb Z,
 \qquad |\pi-A_j|=o(10^{-N_j}).                          \tag{A1}
\]

Then

\[
 \|Q_{N_j}\pi\|_{\mathbb T}
 \le Q_{N_j}|\pi-A_j|=o(1).                             \tag{A2}
\]

Conversely, if \(\|Q_{N_j}\pi\|\to0\), choose a nearest integer
\(z_j\) to \(Q_{N_j}\pi\) and set \(A_j=z_j/Q_{N_j}\).  Exact division
gives

\[
 \frac{|\pi-A_j|}{10^{-N_j}}
 =\frac{10^{N_j}}{Q_{N_j}}\|Q_{N_j}\pi\|
 \longrightarrow0,                                     \tag{A3}
\]

because \(10^{N_j}/Q_{N_j}\to1\).  Moreover,
\(Q_NA\in\mathbb Z\) is equivalent to the reduced denominator of \(A\)
dividing \(Q_N\).  No coprimality hypothesis was omitted.

Finally,

\[
 \liminf_N\|(10^N-c)\pi\|=0
 \quad\Longleftrightarrow\quad c\pi\in K_{10}(\pi).    \tag{A4}
\]

If the right side holds, commutation and closure give
\(cK_{10}(\pi)\subseteq K_{10}(\pi)\).  The joint
\(\langle10,c\rangle\)-orbit of irrational pi is then contained in
\(K_{10}(\pi)\); Furstenberg's nonlacunary-semigroup theorem makes the joint
orbit dense.  Thus \(K_{10}(\pi)=\mathbb T\), which is exactly decimal
disjunctivity/V1.  Density trivially implies the reverse direction.  Hence
the report is correct that (A1) would already solve V1 rather than provide a
weaker intermediate theorem.

## 2. Fixed decimal-primary capacity rederived

For \(p\in\{2,5\}\) and \(N>v_p(c)\),

\[
 v_p(10^N)=N>v_p(c).
\]

The two summands therefore have unequal valuations, so

\[
 v_p(10^N-c)=v_p(c).                                    \tag{A5}
\]

Every divisor of \(Q_N\) has bounded 2- and 5-primary exponents.  This
correctly excludes:

- all sufficiently deep Hutton shadows, whose exact reduced 5-exponent is
  supplied by T63 and whose reduced denominator is odd by T66;
- all sufficiently deep direct \(1/2+1/3\) shadows, whose exact reduced
  2-exponent is \(R-2\); and
- the infinite 5-adic subsequence below for each of the four fixed
  denominator-safe positive identities.

For the last item, let \(S=\sum_i c_ix_i\) be a 5-adic unit and, for
\(e\ge1\), let \(T_e=5^e+2\).  The lower shadow
\(L_{T_e+2}\) includes odd exponents through \(T_e\).  The only included
exponent divisible by \(5^e\) is \(5^e\).  After scaling by \(5^e\), every
other term vanishes modulo 5, whereas Frobenius in \(\mathbb F_5\) gives
\(x_i^{5^e}=x_i\).  Since \(5^e\equiv1\pmod4\), its Taylor sign is positive,
and therefore

\[
 5^eL_{T_e+2}\equiv4S\not\equiv0\pmod5,
 \qquad v_5(\operatorname{den}L_{T_e+2})=e.              \tag{A6}
\]

The independent checker verifies that all four exact linear shadows are
5-adic units and replays (A6) for \(e=1,2,3,4\).  The theorem-level argument,
not this finite range, proves the infinite subsequence.

## 3. Natural-denominator error barrier rederived

Let \(T=R-2\), with \(R\equiv1\pmod4\), and truncate every positive
arctangent series through \(T\).  For \(0<x<1\), the alternating remainder
is strictly larger than its first two omitted terms:

\[
 \arctan x-P_T(x)
 >\frac{x^R}{R}-\frac{x^{R+2}}{R+2}
 =\frac{x^R\{R+2-Rx^2\}}{R(R+2)}
 \ge\frac{2x^R}{R(R+2)}.                                \tag{A7}
\]

Multiplying by the positive identity coefficients and by 4 gives

\[
 \delta_R:=\pi-L_R
 \ge\frac8{R(R+2)}\sum_i c_ix_i^R.                      \tag{A8}
\]

The integer

\[
 D_R=\operatorname{lcm}(1,3,\ldots,T)\prod_i b_i^T      \tag{A9}
\]

is a safe common denominator of \(L_R\); the report does not confuse it with
the fully reduced denominator.  Put \(P=\prod_i b_i\).  Since
\(a_i,c_i\ge1\),

\[
 D_R\delta_R
 \ge\frac8{R(R+2)}P^T\sum_i b_i^{-(T+2)}.               \tag{A10}
\]

AM--GM gives

\[
 \sum_i b_i^{-(T+2)}
 \ge J P^{-(T+2)/J},                                    \tag{A11}
\]

and hence the exponent of \(P\) is exactly
\((T(J-1)-2)/J\).  Because every \(b_i\ge2\), \(P\ge2^J\); for \(J\ge2\)
the weakest case is \(J=2\), yielding

\[
 D_R\delta_R
 \ge\frac{8\,2^{T-1}}{(T+2)(T+4)}
 \ge\frac{32}{35}.                                      \tag{A12}
\]

The last expression increases for \(T\ge3\).  If \(D_R\mid Q_N\), then
\(D_R\le Q_N<10^N\), so \(10^N\delta_R\ge D_R\delta_R\).  This is
incompatible with the little-oh transfer in (A1).  The conclusion is scoped
correctly to synchronizing the safe common denominator; cancellation in the
reduced fraction requires the next argument.

## 4. Private-prime reduced-denominator theorem rederived

Suppose \(p\equiv3\pmod4\) divides exactly one argument denominator
\(b_j\), let \(\beta=v_p(b_j)\ge1\), and assume
\(p\nmid4c_ja_j\).  For odd \(e\), put \(T=p^e\), so \(T\equiv3\pmod4\).
The endpoint term at exponent \(T\) has exact valuation

\[
                         -\beta T-e.                     \tag{A13}
\]

Every earlier term in that component has denominator exponent at most

\[
                 \beta(T-2)+(e-1)<\beta T+e,             \tag{A14}
\]

and all other components are p-integral apart from the exponent denominator,
whose valuation is at most \(e-1\).  Thus (A13) is the unique least valuation
in the complete rational sum.  The nonarchimedean equality for a unique
minimum gives

\[
 v_p(L_{T+2})=-\beta T-e,
 \qquad v_p(\operatorname{den}L_{T+2})=\beta T+e.        \tag{A15}
\]

This is a statement about the **fully reduced denominator**.  If
\(X=\max_i x_i\) has coefficient \(c_*\), (A8) and (A15) imply

\[
 \operatorname{den}(L_{T+2})\,\delta_{T+2}
 \ge\frac{8c_*X^2}{(T+2)(T+4)}p^e(p^\beta X)^T.          \tag{A16}
\]

For the four certificates the relevant pairs are

\[
 (p,pX)=(7,7/3),(11,2),(79,79/11),(127,6).               \tag{A17}
\]

All have \(pX>1\), so (A16) tends to infinity exponentially along odd
\(e\).  The endpoint argument is private in each exact identity, and its
coefficient and numerator are p-units.  This verifies the report's strongest
new obstruction.

It remains deliberately method-specific.  A varying identity might remove
private primes, share them between components, use signed remainder
cancellation, or arrange exceptional reduction.  None of those possibilities
is silently excluded.

## 5. Modular gate and finite replay

If \(p\nmid10\), \(p\mid q_R\), and \(q_R\mid10^N-c\), then

\[
 10^N\equiv c\pmod p,
\]

so necessarily \(c\in\langle10\rangle\subset\mathbb F_p^*\).  Independent
enumeration confirms for \(c=16\): membership holds at \(p=7,127\) and fails
at \(p=11,79\).  The report correctly treats this as a filter, not a
universal obstruction.

The independent checker was written without importing the primary checker.
It verifies the Gaussian-integer branch certificates, all four 5-adic units,
fixed-c primary valuations, the AM--GM lower surrogate, exact 5-adic reduced
denominators, all four private-prime reduced valuations, the four \(R=81\)
rows, and subgroup membership.  Its clean output is:

```text
claim_status=experiment
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
independent_gaussian_identity_checks=12
independent_five_unit_checks=4
independent_fixed_primary_checks=160
independent_five_depth_checks=16
independent_natural_inequality_checks=200
independent_private_prime_checks=32
private name=Hutton p=7 v_p_den=8 floor_log10_q_error_lower=5
private name=split-1 p=11 v_p_den=12 floor_log10_q_error_lower=12
private name=split-2 p=79 v_p_den=80 floor_log10_q_error_lower=300
private name=split-3 p=127 v_p_den=128 floor_log10_q_error_lower=1470
independent_scale_checks=16
independent_subgroup_checks=4
all independent exact assertions passed
```

The primary checker independently reports the same \(R=81\) denominator and
error-margin rows.  These finite checks have status `experiment`; the
asymptotic claims use (A6), (A12), and (A16), not extrapolation.

## 6. Literature applicability rechecked

- DLMF 4.24.E3 gives the arctangent power series used in (A7); the strict
  two-term bound is the elementary alternating-remainder deduction above.
- Gao--Yip, arXiv:2408.02972v2 (revised 2026-05-23), explicitly state that
  distribution for a specific pair \((\xi,\alpha)\) is generally far from
  understood.  Their theorems give counts away from a region under stated
  Diophantine hypotheses, not a shrinking return for \((\pi,10)\).
- Rudnick--Zaharescu, arXiv:math/9912103, prove Poissonian local correlations
  for almost every real multiplier in lacunary sequences.  Their metric
  quantifier cannot be specialized to pi.
- Furstenberg's theorem supplies the semigroup-density implication in
  Section 1 but not the one-generator fixed return.

No cited source is used as a selected-residue or fixed-pi theorem.  The
report's negative literature conclusion is appropriately bounded and makes
no novelty claim.

## 7. Corrections made during audit

The primary mathematical mechanisms did not require correction.  Three
presentation defects were corrected directly in the audited report:

1. Equation (8) originally wrote \(L_{T_e}\), conflicting with the report's
   convention that the subscript is the first omitted exponent.  It now
   correctly reads \(L_{T_e+2}\), with the convention stated explicitly.
2. The finite \(R=81\) paragraph originally said a single shadow could not
   “satisfy (1),” although (1) is an asymptotic sequence condition.  It now
   states the exact finite conclusion: those shadows cannot meet the
   necessary inequality \(10^N\delta_R<1\) under divisibility.
3. The modular gate now explicitly includes both required hypotheses
   \(p\nmid10\) and \(q_R\mid10^N-c\).

These changes narrow notation and quantifiers; they do not upgrade claim
status.

## Sharp audited conclusion

The synchronized rational criterion is exact and equivalent to V1.  The four
fixed positive Machin families fail it for rigorously inspectable reasons:
their decimal-primary exponents exceed fixed-c capacity on relevant
subsequences, their safe common denominator cannot coexist with transferable
error, and a private prime forces the fully reduced denominator/error product
to grow exponentially on an infinite subsequence.

The remaining escape is not “find a faster Machin formula.”  It requires a
depth-varying construction that simultaneously removes private-prime height,
keeps 2/5 exponents bounded, makes the final reduced denominator divide one
\(10^N-c\), and proves enough signed remainder cancellation for
\(o(10^{-N})\).  No audited construction or source provides this.  Therefore
the synchronized-Machin branch passes as a scoped negative `proof sketch`,
while V1 remains a `conjecture`.
