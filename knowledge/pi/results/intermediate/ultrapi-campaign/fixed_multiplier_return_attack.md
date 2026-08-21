# Fixed-multiplier return attack: products compute pi but do not anchor its decimal phase

Audit date: **2026-08-12 UTC**
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

## Outcome and claim status

No fixed multiplier return, decimal cylinder hit, or proof that every finite
decimal word occurs in pi was obtained.  Canonical V1 remains a `conjecture`.

The main new result of this branch is a method-specific negative
`proof sketch`.  Ramanujan's entirely rational, geometrically convergent
series

\[
 \frac{16}{\pi}=\sum_{k\geq0}
  \frac{(42k+5){2k\choose k}^{3}}{2^{12k}}
\tag{1}
\]

looks much better than Wallis for a return argument.  Nevertheless, if
\(A_N\) is the reciprocal of its \(N\)-th partial sum, then the exact
reduced denominator of \(A_N\) grows on the \(4096^N\) scale while the
error decreases only on the \(64^{-N}\) scale.  For every fixed positive
integer \(c\), imposing the strongest possible modular anchor

\[
                  (10^n-c)A_N\in\mathbb Z                 \tag{2}
\]

forces

\[
             (10^n-c)(A_N-\pi)\longrightarrow+\infty,     \tag{3}
\]

not zero.  Thus this rapid rational identity cannot prove a return by exact
denominator divisibility.  The calculation is exact and is given in
Section 4.  It does **not** exclude a new estimate for the nonzero selected
residue of \((10^n-c)A_N\), nor every possible rational approximation.

Wallis has a still larger denominator/error mismatch.  Direct arctangent
shadows have rigorously established growing 2- or 5-primary denominators that
cannot divide \(10^n-c\) for fixed nonzero \(c\).  For BBP, the same
obstruction is elementary at every even truncation depth; the attractive
all-depth valuation formula is supported by exact computation but is not
proved in this note and is not used as a theorem.  Viète, AGM, and Chudnovsky
are fast but algebraic rather than rational at finite depth; once their error
is small enough to transfer, locating their nearest-integer phase is
equivalent to locating the original fixed-pi phase.  These are inspected
obstructions, not an impossibility theorem for all identities.

The exact finite replay is an `experiment`.  The cited source statements are
`literature-checked` as of the audit date.  All deductions in this note are
`proof sketch`; none is a Lean declaration or a `candidate resolution`.

## 1. Exact target and ambiguous quantifiers removed

Let

\[
 K_{10}(x)=\overline{\{10^n x\bmod1:n\geq0\}}\subset\mathbb T.
\]

Fix an integer \(c\geq2\) multiplicatively independent of 10, meaning that
there are no positive integers \(r,s\) with \(c^r=10^s\).  The proposed
foothold is

\[
 c\pi\in K_{10}(\pi).
\tag{4}
\]

This means that there exists an **unbounded** sequence \(n_j\) with

\[
 \boxed{\lim_{j\to\infty}
   \left\|(10^{n_j}-c)\pi\right\|_{\mathbb T}=0.}
\tag{5}
\]

Unboundedness is automatic.  If a finite orbit point satisfied
\(10^N\pi\equiv c\pi\pmod1\), then
\((10^N-c)\pi\in\mathbb Z\); irrationality of pi would force
\(c=10^N\), contrary to multiplicative independence.

Furstenberg's nonlacunary-semigroup theorem makes (4)--(5) **equivalent** to
the whole target V1.  Indeed, a return sequence and commutation give
\(cK_{10}(\pi)\subseteq K_{10}(\pi)\).  Hence the dense joint
\(\langle10,c\rangle\)-orbit lies in \(K_{10}(\pi)\), so that orbit closure
is the full circle.  The converse is immediate.  Therefore a single fixed
independent return would be a breakthrough, but it is not a weaker theorem
that compactness or a product identity supplies for free.

The equivalent restricted-rational statement is worth recording.  With
\(q_n=10^n-c\), (5) says that for some integers \(m_j\),

\[
 \left|\pi-\frac{m_j}{q_{n_j}}\right|=o(q_{n_j}^{-1}).    \tag{6}
\]

Thus the denominator \(10^n-c\), not merely a rapidly convergent formula
for pi, is the essential arithmetic target.

## 2. The two-entry ledger for any rational shadow

Let \(A=P/D\) be a rational approximation in lowest terms.  The only direct
triangle-inequality transfer is

\[
 \|q_n\pi\|_{\mathbb T}
 \leq \|q_nA\|_{\mathbb T}+q_n|\pi-A|.                  \tag{7}
\]

Every proposed identity must therefore pay both entries:

1. **Archimedean resolution:** \(q_n|\pi-A|\to0\).
2. **Ordered congruence:** \(\|q_nP/D\|_{\mathbb T}\to0\).

The strongest way to pay the second entry is the exact anchor

\[
                         D\mid q_n,                       \tag{8}
\]

which makes it zero.  A large denominator, many CRT factors, or rapid
convergence does not imply (8).  If (8) is unavailable, the second entry is
the selected numerator phase that all previous rational-shadow attacks leave
open.  Once the first entry tends to zero, proving that second phase tends to
zero is equivalent to the desired return, up to an error already tending to
zero.

This ledger is also the circularity test for algebraic shadows \(\alpha_j\):

\[
 \big|\|q_n\alpha_j\|_{\mathbb T}
       -\|q_n\pi\|_{\mathbb T}\big|
 \leq q_n|\alpha_j-\pi|.                                \tag{9}
\]

If the right side vanishes and the identity gives no independent integer
anchor for \(q_n\alpha_j\), the algebraic phase problem is simply (5) in a
more complicated representation.

## 3. Wallis and the gamma/reflection family fail before phase analysis

Put

\[
 W_K=2\prod_{k=1}^{K}\frac{4k^2}{4k^2-1}<\pi.           \tag{10}
\]

The omitted product and the telescoping identity

\[
 \sum_{k>K}\frac1{4k^2-1}=\frac1{4K+2}                 \tag{11}
\]

give

\[
 \pi-W_K
 =W_K\left(\prod_{k>K}\left(1+\frac1{4k^2-1}\right)-1\right)
 >\frac1{2K+1}.                                          \tag{12}
\]

Consequently \(q_n(\pi-W_K)\to0\) requires
\(K/q_n\to\infty\), so \(K\) must be much larger than \(10^n\).

On the other hand, for \(K\ge2\), every prime \(K<p\leq2K\) is odd and
occurs to exponent two in the reduced denominator of \(W_K\).  Hence the
prime number theorem gives

\[
 \log\operatorname{den}(W_K)
 \geq2\{\vartheta(2K)-\vartheta(K)\}=(2+o(1))K.          \tag{13}
\]

If the exact anchor (8) held, this denominator would be at most
\(q_n<10^n\), forcing \(K=O(n)\).  Equations (12) and (13) are incompatible
by an exponential margin.  The checker verifies the exact prime valuations
and telescoping identity at finite scale.

Euler's sine product at half-integers and the half-integer gamma/reflection
specializations reduce to the same Wallis/factorial arithmetic.  At a
general rational \(z\),

\[
 \Gamma(z)\Gamma(1-z)=\frac{\pi}{\sin(\pi z)}            \tag{14}
\]

has algebraic \(\sin(\pi z)\), but the gamma product is not a rational
modular anchor for \(q_n\pi\).  The reflection formula rearranges pi; it
does not produce the integer in (6).  The recent regularized Wallis products
likewise introduce exponential, gamma, zeta, or Euler-constant factors and
do not change this lattice mismatch.

## 4. Ramanujan's rational fast series has an exact square-scale obstruction

Define

\[
 S_N=\sum_{k=0}^{N}
       \frac{(42k+5){2k\choose k}^{3}}{2^{12k}},
 \qquad A_N=\frac{16}{S_N}.                              \tag{15}
\]

Ramanujan's positive series (1) gives \(S_N<16/\pi\), hence
\(A_N>\pi\).  Put

\[
 U_N=2^{12N}S_N
 =\sum_{k=0}^{N}(42k+5){2k\choose k}^{3}2^{12(N-k)}.
\tag{16}
\]

Let \(s_2(N)\) denote the number of ones in the binary expansion of \(N\).
Kummer's elementary central-binomial valuation is

\[
 v_2{2k\choose k}=s_2(k).                                \tag{17}
\]

The final term of (16) has valuation \(3s_2(N)\).  It is the unique term of
minimum valuation.  Indeed, for \(k=N-d<N\), binary digit-sum
subadditivity gives

\[
 s_2(N)\leq s_2(k)+s_2(d),\qquad s_2(d)\leq d,
\]

and therefore

\[
 12d+3s_2(k)\geq3s_2(N)+12d-3s_2(d)>3s_2(N).             \tag{18}
\]

Thus

\[
 \boxed{v_2(U_N)=3s_2(N)},                               \tag{19}
\]

and the reduced denominator of \(A_N\) is exactly

\[
 D_N=\frac{U_N}{2^{3s_2(N)}}.
\tag{20}
\]

All summands in (16) are positive, and its \(k=0\) summand yields

\[
 D_N\geq5\,2^{12N-3s_2(N)}
       \geq\frac{5\,2^{12N}}{(N+1)^3}.                  \tag{21}
\]

This is the denominator half of the ledger.

For the error half, the first omitted positive term and
\({2m\choose m}\geq4^m/(2m+1)\) give, with \(m=N+1\),

\[
 \frac{16}{\pi}-S_N
 \geq\frac{(42m+5){2m\choose m}^{3}}{2^{12m}}
 \geq\frac{42m+5}{64^m(2m+1)^3}.                        \tag{22}
\]

Since \(S_N<16/\pi<6\),

\[
 A_N-\pi
 =\frac{16(16/\pi-S_N)}{S_N(16/\pi)}
 >\frac49\frac{42m+5}{64^m(2m+1)^3}.                    \tag{23}
\]

Now fix \(c\geq1\), put \(q_n=10^n-c>0\), and suppose the exact anchor
\(q_nA_N\in\mathbb Z\) holds.  Because (20) is reduced, \(D_N\mid q_n\).
Equations (21) and \(D_N<10^n\) imply

\[
 64^N<10^{n/2}(N+1)^{3/2}/\sqrt5,                        \tag{24}
\]

and also \(N=O(n)\).  For all sufficiently large \(n\),
\(q_n>10^n/2\).  Substitution of (24) into (23) gives

\[
 q_n(A_N-\pi)
 \gg \frac{10^{n/2}}{(N+1)^{7/2}}
 \longrightarrow+\infty.                                \tag{25}
\]

If \(N\) remains bounded, the same conclusion is immediate because
\(A_N-\pi\) stays positive.  This proves the scoped assertion (3).

The important feature is not merely that a denominator is large.  The
tail has scale \(64^{-N}\), but the reciprocal's exact reduced denominator
has scale \(4096^N=64^{2N}\), up to polynomial factors.  Divisibility by
\(10^n-c\) spends the entire denominator budget twice as fast as convergence
earns transferable accuracy.

Without exact divisibility, one is left with
\(\|(10^n-c)A_N\|\).  No checked source controls that selected numerator,
and (7) shows that controlling it at a transferable scale would be the
actual fixed-pi return rather than a consequence of (1).

## 5. BBP and fixed-prime arctangent denominators

For the standard rational BBP partial sums

\[
 B_N=\sum_{k=0}^{N}\frac1{16^k}
 \frac{120k^2+151k+47}
 {(2k+1)(4k+3)(8k+1)(8k+5)},                             \tag{26}
\]

exact computation suggests the all-depth valuation

\[
 v_2(\operatorname{den}B_N)=4N-v_2(N+1).                 \tag{27}
\]

The branch checker verifies (27) for \(1\le N\le60\), and the independent
checker extends this to \(N\le400\).  This remains an experiment: neither a
general induction nor a source for (27) is supplied here, so the formula is
not used below as a theorem.

There is a simple unconditional even-depth statement.  The denominator of
the combined coefficient in (26) is odd, while

\[
 120N^2+151N+47\equiv1\pmod2\qquad(N\ {\rm even}).
\]

Thus at even \(N\), the last summand has two-adic valuation \(-4N\);
every preceding summand has valuation at least \(-4N+4\).  The minimum is
unique, and therefore

\[
 v_2(\operatorname{den}B_N)=4N\qquad(N\ {\rm even}).      \tag{27a}
\]

For fixed nonzero \(c\) and all \(n>v_2(c)\),

\[
 v_2(10^n-c)=v_2(c).                                     \tag{28}
\]

Hence \(\operatorname{den}B_N\nmid10^n-c\) along every growing sequence of
even truncation depths.  A bounded \(N\) cannot pay the BBP transfer error.
The present argument does not exclude an exact anchor chosen only at odd
depths; doing so would require a proof of (27) or another odd-depth
valuation theorem.  The usual choice \(c=16\) still enjoys the exponentially
small BBP shadowing error, but the surviving rational residue is exactly the
already-audited condition
\(\liminf\|(10^n-16)B_n\|=0\), equivalent to V1.

The same elementary issue does rule out direct Taylor shadows with a growing
2- or 5-primary reduced denominator.  The Euler \(1/2+1/3\) shadow has exact
\(v_2(\operatorname{den})=R-2\), while the Hutton shadow has an unbounded
exact 5-primary decimal transient.  Since (28) and its 5-adic analogue are
fixed by \(c\), neither denominator can divide \(10^n-c\) at increasing
depth.

There is a useful more general warning for a fixed prime \(p\nmid10c\).
Yu's explicit theorem on p-adic logarithmic forms, applied to

\[
 \Xi=10^n c^{-1}-1,
\]

gives, for fixed \(p,c\) with \(10^n\ne c\),

\[
                         v_p(10^n-c)=O_{p,c}(\log n).      \tag{29}
\]

Therefore a rational identity whose reduced denominator contains a proven
fixed factor \(p^{\kappa R}\), and whose tail needs \(R\asymp n\), cannot
use exact divisibility: (29) would force \(R=O(\log n)\).  This applies to a
single fixed rational arctangent denominator when its p-primary survival is
proved.  It does not apply merely because many *varying* primes occur, and it
does not replace the missing global numerator theorem for recursively split
Machin identities.

As an `experiment`, the checker lifts the concrete compatible congruence
\(10^n\equiv3\pmod{7^M}\).  The least compatible exponents for
\(1\leq M\leq12\) begin

\[
 1,13,265,2029,4087,32899,32899,738793,20503825,\ldots . \tag{30}
\]

This vividly displays the wrong synchronization: acquiring linearly many
7-adic denominator digits can cost an exponentially large decimal exponent,
whereas an ordinary Taylor tail improves only exponentially in its depth.
The finite list is illustrative only; (29), not the experiment, is the
theorem-level input.

## 6. Viète, AGM, and Chudnovsky: fast algebraic shadows remain rank one

The \(h\)-factor Viète product gives the algebraic approximation

\[
 V_h=2^{h+1}\sin\frac{\pi}{2^{h+1}},\qquad
 \pi-V_h\sim\frac{\pi^3}{24\,4^h}.                       \tag{31}
\]

Thus \(q_n(\pi-V_h)\to0\) is easy if
\(h>(\log_4 10+o(1))n\).  But for every nontrivial depth \(h\ge1\),
\(V_h\) is an irrational cyclotomic algebraic number, so \(q_nV_h\) is never
an integer.  Once
the transfer error vanishes, (9) says that proving
\(\|q_nV_h\|\to0\) is equivalent to the original return.  Taking an
algebraic trace does not isolate this real conjugate; it adds all the other
cyclotomic conjugates.

The Brent--Salamin AGM doubles the number of correct digits at each step,
so only \(O(\log n)\) radical iterations are needed to transfer at scale
\(q_n\).  Its finite iterates are again algebraic numbers in a growing
radical tower, not rational numbers with a denominator dividing \(q_n\).
Rapid convergence pays only the first entry of (7).

The Chudnovsky truncation has the same structural issue in a quadratic
extension: its standard finite shadow is a rational multiple of
\(\sqrt{10005}\).  Its roughly fourteen decimal digits per term make
archimedean transfer inexpensive, but there is no exact integer anchor for
\(q_n\sqrt{10005}\) times the selected rational coefficient.  Replacing the
square root by a Pell or continued-fraction rational approximation introduces
a second denominator and the new unsolved requirement that its reduced
denominator divide, or have a controlled residue against, \(10^n-c\).

Gaussian-integer proofs of Machin identities certify the **angle sum** and
remove branch ambiguity.  They do not turn the Taylor shadow into an integer
over \(10^n-c\).  Similarly, the sine/reflection identities are periodic
modulo \(\pi\), whereas (5) asks for distance modulo the integer lattice.
Euler's exact relation \(e^{i\pi}=-1\) therefore controls the wrong character:
it makes \(e^{iq\pi}=\pm1\) for integer \(q\), but the target character is
\(e^{2\pi i q\pi}=e^{2\pi^2iq}\).

## 7. Dated primary-source search

The search was rerun on **2026-08-12 UTC** before treating any product as a
new route.

| source | checked statement | exact applicability here |
|---|---|---|
| [Furstenberg, *Disjointness in ergodic theory, minimal sets, and a problem in Diophantine approximation* (1967)](https://doi.org/10.1007/BF01692494) | Nonlacunary multiplicative semigroups have dense irrational orbits. | Gives the equivalence (4)--(5) to V1; it does not give the fixed return. |
| [Ramanujan, *Modular equations and approximations to pi* (1914), equation (29)](https://ramanujan.sirinudi.org/Volumes/published/ram06.html) | The positive rational series (1). | Supplies the identity audited in Section 4; the denominator/error obstruction is the new local deduction. |
| [Bailey--Borwein--Plouffe, *On the rapid computation of various polylogarithmic constants*](https://doi.org/10.1090/S0025-5718-97-00856-9) | The base-16 BBP formula for pi. | Digit extraction and a fast tail do not settle the decimal selected residue. |
| [Lagarias, *On the normality of arithmetical constants*](https://arxiv.org/abs/math/0101055) | Density of the relevant remainder orbit is the digit-density condition; stronger BBP dynamical conclusions retain an unproved hypothesis. | Confirms that no unconditional BBP return theorem is being omitted. |
| [Yu, *p-adic logarithmic forms and group varieties II* (1999), Theorem 1](https://doi.org/10.4064/aa-89-4-337-378) | Explicit \(p\)-adic order bound proportional to \(\log B\) for a nonzero algebraic multiplicative form. | With fixed \(10,c,p\), yields (29); it is not a global CRT-distribution theorem. |
| [Salamin, *Computation of pi using arithmetic-geometric mean* (1976)](https://doi.org/10.1090/S0025-5718-1976-0404124-9) and [Brent, *Fast multiple-precision evaluation of elementary functions* (1976)](https://doi.org/10.1145/321941.321944) | Quadratically convergent AGM computation of pi. | Pays the error term, not the integer-phase term in (7). |
| [Sondow--Yi, *New Wallis- and Catalan-Type Infinite Products*](https://arxiv.org/abs/1005.2712) | Gamma-derived Wallis-type products for pi-related constants; Catalan-type products there concern powers of \(e\). | No denominator \(10^n-c\), orbit-return, or digit theorem is supplied. |
| [Holcombe, *A Regularised Wallis Hierarchy* (2026)](https://arxiv.org/abs/2606.23973) | Regularized products involving pi together with exponential/zeta constants. | The new factors are not rational modular anchors and do not change (7). |
| [Milla, *A Detailed Proof of the Chudnovsky Formula*](https://arxiv.org/abs/1809.00533) | A modern proof and exact form of the Chudnovsky series. | Its finite pi shadow retains \(\sqrt{10005}\); no fixed decimal return follows. |

Searches combining *fixed multiplier return*, *fractional parts of powers
times pi*, *Wallis/Gamma/reflection*, *Viète/AGM*, *Ramanujan/Chudnovsky*,
*BBP*, and *p-adic logarithmic forms* located no primary theorem proving
\(c\pi\in K_{10}(\pi)\) for any integer \(c\) independent of 10.  This is a
bounded negative search result, not a novelty or impossibility claim.

## 8. Exact finite replay

The companion checker is
[`fixed_multiplier_return_check.py`](fixed_multiplier_return_check.py).  It
uses integer arithmetic and Python `Fraction` for all exact assertions.  It
does not numerically certify Ramanujan's infinite identity or Furstenberg's
theorem; those are the cited analytic inputs.  A clean run reports:

```text
claim_status=experiment
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
wallis_prime_denominator_checks=695
wallis_tail_telescoping_checks=237
ramanujan_exact_two_adic_checks=81
ramanujan_reduced_denominator_checks=81
ramanujan_first_tail_lower_checks=81
ramanujan_anchor_equivalence_checks=2574
ramanujan_small_exact_anchor_hits=[]
bbp_exact_two_adic_checks=60
bbp_fixed_c_divisibility_exclusions=298
seven_adic_lifted_exponents=1,13,265,2029,4087,32899,32899,738793,20503825,124270243,1092756811,2787608305
all exact assertions passed
```

The absence of small anchor hits is only an `experiment` and is not used in
the proof-sketch obstruction.  The Ramanujan and Wallis valuation formulae,
the even-depth BBP valuation (27a), and the stated inequalities carry the
deductions above.  The stronger all-depth BBP pattern (27) remains an
experiment.

## Sharp conclusion

The fixed-multiplier route is normalized to one decisive sufficient
condition:

\[
 \exists c\perp_{\rm mult}10\quad
 \liminf_n\|(10^n-c)\pi\|=0.                             \tag{32}
\]

By Furstenberg this condition is already equivalent to V1.  Classical
identities do provide exceptionally accurate shadows, but each audited
family misses a different entry of the exact ledger:

- Wallis: the transferable depth is exponentially larger than any divisor
  of \(10^n-c\) can be.
- Ramanujan's all-rational fast series: exact denominator growth is the
  square of its tail scale, and an exact anchor makes the transferred error
  diverge.
- BBP/direct arctangent shadows: BBP has an exact even-depth 2-primary
  obstruction (with the stronger all-depth formula still an experiment);
  the direct shadows have proved growing 2- or 5-primary denominators that
  cannot divide \(10^n-c\).
- Coprime arctangent coordinates: p-adic lifting has only logarithmic
  valuation in the decimal exponent for a fixed prime, and global selected
  numerators remain uncontrolled.
- Viète, AGM, Chudnovsky, gamma, and Gaussian products: fast finite shadows
  are algebraic or special-function values without an independent integer
  anchor, so their nearest-integer phase is the original rank-one problem.

A viable continuation must therefore produce genuinely new **ordered
congruence information tied to the denominator \(10^n-c\)**.  Another
identity, convergence acceleration, radical expression, denominator-size
bound, or collection of local CRT factors does not by itself move the fixed
Archimedean phase toward an integer.
