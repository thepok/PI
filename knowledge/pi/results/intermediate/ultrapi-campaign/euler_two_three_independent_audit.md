# Independent audit: the \(1/2+1/3\) arctangent shadow

Audit date: **2026-08-12 UTC**  
Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt)  
Audit scope: [euler_two_three_attack.md](euler_two_three_attack.md), the
submitted exact replay, and an independent exact replay

## Verdict

**PASS at the stated `proof sketch` level after five precision
corrections.** The arctangent identity and alternating bracket, exact
two-primary denominator exponent, decimal preperiod wall, three-primary
certificate and power subsequence, multiband local law, fixed-band radical
asymptotic, and selected-prime CRT projection all rederive correctly.

The central negative conclusion is now stronger and exact: for every
nonempty word length, the scaled bracket at the first post-transient shift is
wider than a whole decimal cylinder, not merely wider than the note's
factor-two safety threshold. Therefore no post-transient rational period can
certify a digit of pi through this bracket.

This does **not** prove V1. The remaining transient selected-numerator hit is
equivalent to V1 when required for every word. V1 remains a `conjecture`;
the audited mathematics remains a `proof sketch`; the finite replays are
`experiment`; and this branch is neither `machine-checked` nor a
`candidate resolution`.

The corrected artifact pins are:

| Artifact | SHA-256 |
|---|---|
| [euler_two_three_attack.md](euler_two_three_attack.md) | `f8832472454e0cca9055ec51befe1e9a41e1d3566673fd76b40edf258217a95d` |
| [euler_two_three_check.py](euler_two_three_check.py) | `573ae211ef7518f5a9342dccc1f8d8a911367ce595f21dedd4a075a9245ab9a3` |
| [euler_two_three_independent_check.py](euler_two_three_independent_check.py) | `088a3d06607bbb4177872a755b6fd4f57e2272775289c20906ce09099aa2ccfb` |

## Corrections made during review

1. The local-law hypothesis now says \(\sqrt R<p\le R\). Previously it only
   said \(p^2>R\), under which the defining set for \(m_p\) is empty when
   \(p>R\). This was a genuine missing endpoint quantifier, although every
   use and every computed case already had \(p\le R\).
2. The safe horizon now has the explicit convention \(J_{K,\ell}=-1\) when
   its nonnegative admissible set is empty. Such cases really occur for
   small \(K\) or large \(\ell\); the submitted checker already represented
   them as `-1`, while the original displayed maximum was undefined.
3. The preperiod obstruction was strengthened from
   \(10^{R-2}W_K>10^{-\ell}/2\) to
   \(10^{R-2}W_K>10^{-\ell}\). The former only excludes the chosen safety
   test; the latter proves that no alignment inside an entire cylinder can
   work at or after the preperiod.
4. The modulus behind \(N=\Theta(\log G)\) is now the explicit product
   \(G_K^*\) of all noncancelling certified primes above \(\sqrt R\). The
   fixed-band squeeze proves \(\log G_K^*=R+o(R)\). An arbitrary finite
   selected set from the preceding CRT paragraph would not justify the
   displayed \(\Theta(\log G)\) relation.
5. The exponential notation and the final normality comparison are now
   explicit. The latter is a precise Weyl average, not an undefined
   reference to selected-numerator sums.

The submitted checker was amended to exercise the empty-horizon boundary,
the exact last-admissible inequality, the full-cylinder wall, the factored
width, and the rational tangent-addition input. A separate implementation
was added rather than importing the submitted functions.

## 1. Identity, bracket, and exact horizon

For \(x=1/2\) and \(y=1/3\), exact rational arithmetic gives

\[
 {x+y\over1-xy}=1.
\]

Both arctangents are positive and their sum lies in \((0,\pi/2)\), so the
tangent addition formula identifies the sum with \(\pi/4\). This independently
recovers the mathlib theorem
`Real.arctan_inv_2_add_arctan_inv_3`.

When \(R=4K+3\), each Gregory series is cut after \(2K+2\) terms. Its final
included term is negative and the next is positive. Applying the alternating
remainder inequality to the two series separately gives

\[
 E_K<\pi<U_K,\qquad
 W_K=U_K-E_K
 ={1+(2/3)^{R+2}\over(R+2)2^R}.
\]

Let

\[
 T_{K,\ell}=\log_{10}{1\over2\,10^\ell W_K}.
\]

The strict defining inequality for the safe horizon is \(j<T_{K,\ell}\).
Consequently

\[
 J_{K,\ell}=\max(-1,\lceil T_{K,\ell}\rceil-1),
\]

which verifies both the empty-set convention and the strict endpoint. For
fixed \(\ell\), direct substitution of \(W_K\) yields the slightly sharper
form

\[
 J_{K,\ell}=R\log_{10}2+\log_{10}R+O_\ell(1),
\]

and hence the report's \(R\log_{10}2+O(\log R)\).

## 2. Exact two-primary wall

The \(r=R\), base-\(2\) summand has valuation \(2-R\). Every earlier
base-\(2\) summand has valuation at least \(4-R\), while every base-\(3\)
summand has valuation \(2\). The minimum is unique, so the nonarchimedean
triangle inequality is exact:

\[
 v_2(E_K)=2-R,\qquad v_2(Q_K)=R-2.
\]

A common denominator divides
\(2^R3^R\operatorname{lcm}(1,3,\ldots,R)\), so

\[
 v_5(Q_K)\le\lfloor\log_5R\rfloor\le R-2.
\]

Thus the minimal decimal preperiod is exactly \(A_K=R-2\). At its first
post-transient shift,

\[
 10^{R-2}W_K
 ={5^R\over100(R+2)}\left(1+(2/3)^{R+2}\right).
\]

The inequality \(5^R>10(R+2)\) holds at \(R=3\) and is preserved when \(R\)
increases. Hence the last display is \(>1/10\), which is at least the width
\(10^{-\ell}\) of every nonempty decimal cylinder. Since scaled width grows
with the shift, no bracket at \(j\ge R-2\) can fit in such a cylinder. This
validates the report's main separator without relying on favorable or
unfavorable endpoint alignment.

## 3. Three-primary certificate and exact subsequence

Write \(r=3^{\nu(r)}u_r\), where \(u_r\) is coprime to 3, and let

\[
 M_R=\max_{r\le R,\ r\text{ odd}}(r+\nu(r)),\qquad
 U_R=\operatorname{lcm}_{r\le R,\ r\text{ odd}}u_r.
\]

Multiplication by \(U_R2^R3^{M_R}\) turns the two terms at exponent \(r\)
into

\[
 4\chi_4(r)(3^r+2^r){U_R\over u_r}
 2^{R-r}3^{M_R-r-\nu(r)},
\]

exactly the report's integer \(N_R\). Since \(3\nmid U_R2^R\), reduction of
this common fraction gives

\[
 v_3(E_K)=v_3(N_R)-M_R,\qquad
 v_3(Q_K)=\max(0,M_R-v_3(N_R)).
\]

For \(R=3^e\) with odd \(e\), the endpoint has height \(R+e\). Every earlier
odd \(r\le R-2\) has height at most \(R+e-3\), while all base-\(2\) terms are
far less singular. The endpoint coefficient \(3^R+2^R\) is a 3-unit, so it
is the unique minimum and

\[
 v_3(Q_K)=R+e.
\]

LTE gives \(v_3(10^t-1)=2+v_3(t)\). Because the projected numerator is a
3-unit, its exact multiplication-by-10 period modulo \(3^{R+e}\) is
\(3^{R+e-2}\). This coordinate period is correct but begins too late to
transfer through the bracket.

## 4. Multiband law and radical asymptotic

Let \(\sqrt R<p\le R\) be prime, \(p>3\), and let \(m_p\) be the largest odd
integer with \(m_pp\le R\). Since \(m_p<p\), every denominator occurring in
\(C_{m_p}\) is a \(p\)-unit. After multiplying \(E_K\) by \(p\), all terms
with \(p\nmid r\) vanish modulo \(p\). The remaining exponents are \(r=mp\)
with odd \(m\le m_p\), each with \(v_p(r)=1\). Character multiplicativity
and Fermat reduction give

\[
 pE_K\equiv\chi_4(p)
 4\sum_{m\le m_p,\ m\text{ odd}}{\chi_4(m)\over m}
 \left(2^{-m}+3^{-m}\right)
 =\chi_4(p)C_{m_p}\pmod p.
\]

The summands defining each fixed \(C_M\) pair into positive differences, so
\(C_M\ne0\). Also \(v_p(E_K)\ge-1\). Therefore

\[
 v_p(E_K)=-1
 \quad\Longleftrightarrow\quad
 p\nmid\operatorname{num}(C_{m_p});
\]

in the complementary case \(p\) is absent from the reduced denominator.
For \(R/3<p\le R\), \(m_p=1\) and \(C_1=10/3\), so only the fixed prime 5
can cancel.

For fixed odd \(L\), every prime in \((R/L,R]\) has \(m_p\) in a fixed finite
list and eventually exceeds all prime divisors of the corresponding fixed
numerators and denominators. Hence every such prime occurs exactly once.
The prime-number-theorem squeeze is

\[
 \vartheta(R)-\vartheta(R/L)+O_L(1)
 \le\log\operatorname{rad}_{(6)}(Q_K)\le\vartheta(R)+O(1).
\]

First letting \(R\to\infty\) for fixed \(L\), then letting \(L\to\infty\),
proves

\[
 \log\operatorname{rad}_{(6)}(Q_K)=R+o(R).
\]

The same squeeze applies to the explicit certified product \(G_K^*\). No
uniform assertion about prime divisors of \(C_M\) for growing \(M\) is used.

## 5. CRT projection and why it is insufficient

For any selected product \(G\), write \(Q_K=GC\). Exact exponent one at
each selected prime gives \((G,C)=1\). If \(p\mid G\), the local law and
\(Q_K/p=C(G/p)\) yield

\[
 P_K\equiv C\,\chi_4(p)C_{m_p}{G\over p}\pmod p.
\]

The primewise congruences combine to the stated unique residue
\(P_KC^{-1}\pmod G\). The additive CRT factorization

\[
 e_{GC}(x)=e_G(xC^{-1})e_C(xG^{-1})
\]

is exact. It also displays the unresolved issue: the complementary factor
contains \(2^{R-2}\), changes with the same shift, and can correlate with
the selected-prime factor. Prime projections do not turn a real interval
modulo \(GC\) into a product interval.

The denominator-only counterexample is valid. Since

\[
 Q_K\ge2^{R-2}\operatorname{rad}_{(6)}(Q_K)
       =\exp((1+\log2)R+o(R))
\]

and \(10^{J_{K,\ell}}=\exp((\log2)R+o(R))\), the rational \(1/Q_K\) has all
of its transferable states within \(\exp(-R+o(R))\) of zero. It has the same
denominator data but deliberately not the actual local projection. Thus it
refutes denominator-uniform coverage, while leaving only the selected
numerator as a possible source of progress.

## 6. Replay and source checks

The corrected submitted checker ended with `all exact checks passed` and
reported 121 bracket/primary rows, 9,265 local congruences, 9,170 nonzero
valuation cases, 6,066 upper-band cases, and 9,170 CRT coordinates.

The independent checker does not import the submitted one. It ended with
101 primary/bracket rows, 52 empty-horizon convention cases, 5,448 local
rows, 5,381 exact-valuation rows, 5,381 CRT rows, the three-primary pairs
\((3,4),(27,30),(243,248)\), and `all independent exact checks passed`.

These are `experiment`, including the finite radical ratios. They test
signs, exact cancellation, strict horizon endpoints, local normalizations,
and CRT recombination; they do not prove the PNT asymptotic or V1.

The immutable target hash was independently rechecked as
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The local mathlib source contains
`Real.arctan_inv_2_add_arctan_inv_3`. Calcut's primary-history PDF was
fetched afresh and matched the report's SHA-256
`d650da61527c78c67caca06758363280bac7303cb2b553fc786914ddf3a4886f`;
its introduction attributes this identity to Machin (1706). Vandehey's
versioned arXiv PDF also matched the pinned SHA-256
`28f10a84ee2038d09af33f1509e74386d70c96baee158143b0924c80e3cc1b7c`;
Theorems 1.4 and 7.2 assume a fixed finite prime set and require a
superlogarithmic length, while its quoted Bourgain theorem has a
positive-power length hypothesis. Those hypotheses do not cover the
logarithmic-length, growing-prime-support orbit here. The report's dated
bounded search is therefore `literature-checked`, not a novelty claim.

## Bottom line

The \(1/2+1/3\) shadow really has a certified prime radical of natural-log
size \(R+o(R)\), but its exact dyadic preperiod is \(R-2\), whereas its
transferable prefix has only \(R\log_{10}2+O(\log R)\) decimal shifts. The
full-cylinder inequality proves that the periodic phase cannot help at all.
Inside the transient, the exact local residues determine only one CRT
projection; the correlated dyadic/complementary coordinate remains
uncontrolled. Proving the required actual-numerator localization would be
the missing V1 result, not a consequence already supplied by the radical,
period, or cited exponential-sum literature.
