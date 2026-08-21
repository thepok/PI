# The \(1/2+1/3\) arctangent shadow: a large radical trapped behind the decimal transient

Audit date: **2026-08-12 UTC**
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Provenance: Marcel's immutable local question has no external source URL;
none is invented here. This note follows the fields of
[`problems/TEMPLATE.md`](../../problems/TEMPLATE.md) inside the existing
problem record rather than creating a second problem statement.

## Outcome and claim status

No proof that every finite decimal word occurs in pi was obtained. The
canonical V1 statement remains a `conjecture`.

The identity

\[
 {\pi\over4}=\arctan(1/2)+\arctan(1/3)                 \tag{1}
\]

does give a cleaner and larger denominator radical away from \(2\) and \(3\)
than the Hutton
shadow. It also has a fatal timing obstruction for the most tempting route:

* if \(R=4K+3\), then for each fixed nonempty word length the safe
  bracket-transfer horizon is \(R\log_{10}2+O(\log R)\);
* the reduced denominator of the lower shadow has exact two-primary
  exponent \(R-2\), and hence exact decimal preperiod \(R-2\);
* every position whose bracket is narrow enough to certify a nonempty word
  occurs **strictly before** that preperiod ends.

Thus no coprime post-transient orbit, complete period, or estimate restricted
to that period can certify a digit of pi from these shadows. This does not
rule out analysis of the transient digits themselves. It identifies that
analysis as the unresolved selected-numerator problem.

There is substantial exact arithmetic structure inside the transient. For
primes \(\sqrt R<p\le R\), an explicit finite local constant determines
\(pE_K\pmod p\). A fixed-band argument and the prime number theorem then give

\[
 \log\operatorname{rad}_{(6)}(\operatorname{den}E_K)
     =R+o(R),\qquad
 \log_{10}\operatorname{rad}_{(6)}(\operatorname{den}E_K)
     ={R\over\log 10}+o(R).                            \tag{2}
\]

The decimal size in (2), \(0.434294\ldots R\), exceeds the transferable
prefix \(0.301029\ldots R\). This scale comparison is genuine, but it does
not imply interval coverage: the prime coordinate is only one correlated
CRT projection of the actual numerator.

The bracket, valuation, local-congruence, radical, and CRT arguments below
are a `proof sketch`: their elementary derivations are written out, but no
new Lean declarations have been made. The dated source search is
`literature-checked`. The companion finite replay is an `experiment`.
Nothing here is a `candidate resolution`.

Historical note: this audit keeps the operational filename requested for
the “Euler \(2/3\)” attack, but the primary history source located below
attributes (1) to Machin (1706), not Euler. Mathlib names the theorem
neutrally as `Real.arctan_inv_2_add_arctan_inv_3`.

## 1. Normalized target and quantifiers

Write

\[
 \pi=3+\sum_{n\ge0}d_n(\pi)10^{-(n+1)},
 \qquad d_n(\pi)\in\{0,\ldots,9\}.
\]

The canonical target is

\[
 \forall\ell\ge0\ \forall c<10^\ell\ \exists j\ge0:
 \left\lfloor10^\ell\{10^j\pi\}\right\rfloor=c.       \tag{V1}
\]

The code \(c\) is padded to length \(\ell\), so leading zeroes count;
occurrence is contiguous; and \(\ell=0\) is vacuous. Pi is irrational, so
no terminating/nonterminating decimal convention is involved.

Three quantifier distinctions matter here.

1. A complete rational period may depend on \(K\), but its positions are
   useful only if the bracket is still narrow after scaling to them.
2. A theorem for every numerator with the same denominator is stronger than
   a theorem for the selected numerator of \(E_K\), and is false at the
   required length.
3. Hitting each fixed word for some pair \((K,j)\) is V1; discrepancy tending
   to zero for the whole transferable prefix is the stronger normality
   problem.

No argument below interchanges these readings.

## 2. Exact alternating shadows and bracket width

For odd \(r\), put

\[
 \chi_4(r)=(-1)^{(r-1)/2}.
\]

With \(R=4K+3\), define the rational lower shadow

\[
 E_K=4\sum_{\substack{1\le r\le R\\r\ {\rm odd}}}
 {\chi_4(r)\over r}\left({1\over2^r}+{1\over3^r}\right). \tag{3}
\]

There are \(2K+2\) terms in each alternating arctangent series. The last
included term is negative and the next term, at exponent \(R+2\), is
positive. Therefore (1) and the alternating-series inequalities give

\[
 E_K\le\pi\le U_K,
\]

where the exact adjacent width is

\[
 \begin{aligned}
 W_K:=U_K-E_K
  &={4\over(R+2)2^{R+2}}+{4\over(R+2)3^{R+2}}\\
  &={1+(2/3)^{R+2}\over(R+2)2^R}.                       \tag{4}
 \end{aligned}
\]

For a word length \(\ell\ge1\), retain the factor-two safety margin and let

\[
 J_{K,\ell}=\max\bigl(\{-1\}\cup
 \{j\in\mathbb Z_{\ge0}:10^jW_K<10^{-\ell}/2\}\bigr). \tag{5}
\]

Thus \(J_{K,\ell}=-1\) when even the unshifted bracket misses the safety
threshold. This convention matters for small \(K\) or large \(\ell\), while
the following asymptotic is for fixed \(\ell\).

If the lower endpoint at such a \(j\) lies in the left half of a decimal
cylinder of length \(10^{-\ell}\), the whole scaled bracket lies in that
cylinder and certifies the word for pi. From (4), for fixed \(\ell\),

\[
 J_{K,\ell}=R\log_{10}2+O(\log R)
            =0.301029995\ldots R+O(\log R).             \tag{6}
\]

Finite evidence is not needed for (4)--(6); they are direct identities and
inequalities.

## 3. Exact two-primary valuation and the preperiod wall

In the \(q=2\) series, the term at \(r=R\) has two-adic valuation

\[
 v_2\!\left({4\chi_4(R)\over R2^R}\right)=2-R.         \tag{7}
\]

Every earlier \(q=2\) term has \(r\le R-2\), hence valuation at least
\(4-R\). Every \(q=3\) term has valuation at least \(2\), because \(r\) and
\(3^r\) are odd. Thus (7) is the unique minimum in the entire sum, and the
ultrametric inequality is exact:

\[
 \boxed{v_2(E_K)=2-R.}                                  \tag{8}
\]

If \(E_K=P_K/Q_K\) in lowest terms, (8) says

\[
 v_2(Q_K)=R-2.                                          \tag{9}
\]

A natural common denominator for (3) divides
\(2^R3^R\operatorname{lcm}(1,3,\ldots,R)\). Consequently

\[
 v_5(Q_K)\le\lfloor\log_5R\rfloor<R-2+1.              \tag{10}
\]

For every \(R\ge3\), (9)--(10) prove that the exact preperiod length of the
base-10 expansion of \(E_K\) is

\[
 A_K=\max(v_2(Q_K),v_5(Q_K))=R-2.                       \tag{11}
\]

This is not merely an asymptotic mismatch. At the first post-transient
position, (4) gives the stronger full-cylinder obstruction

\[
 10^{R-2}W_K
 ={5^R\over100(R+2)}\left(1+(2/3)^{R+2}\right)
 >{1\over10}\ge 10^{-\ell}\ge {10^{-\ell}\over2}     \tag{12}
\]

for every \(R\ge3\) and every \(\ell\ge1\). The first strict inequality
follows from \(5^R>10(R+2)\), whose base case is \(R=3\) and which persists
on increasing \(R\). Since the scaled width only grows with \(j\), (12)
proves not only the safe-horizon bound

\[
 \boxed{J_{K,\ell}<A_K=R-2\quad(\ell\ge1).}             \tag{13}
\]

It also proves that at and after \(A_K\), the scaled bracket is wider than
the entire length-\(10^{-\ell}\) cylinder, so no favorable alignment can
rescue a post-transient position. Therefore every bracket-certifiable
nonempty-word position belongs to the nonperiodic dyadic transient. Waiting
for the rational expansion's periodic part is not an available proof
strategy.

## 4. Exact three-primary certificate and an infinite exact subsequence

The three-primary valuation has genuine cancellations and is not always a
simple function of \(R\). It nevertheless has an exact integer certificate.
For odd \(r\le R\), let

\[
 \nu(r)=v_3(r),\qquad
 M_R=\max_{r\le R,\ r\ {\rm odd}}(r+\nu(r)),\qquad
 U_R=\operatorname{lcm}_{r\le R,\ r\ {\rm odd}}
       {r\over3^{\nu(r)}}.                              \tag{14}
\]

Define the integer

\[
 N_R=4\sum_{r\le R,\ r\ {\rm odd}}
 \chi_4(r)(3^r+2^r)
 {U_R\over r/3^{\nu(r)}}
 2^{R-r}3^{M_R-r-\nu(r)}.                              \tag{15}
\]

Termwise common-denominator arithmetic gives the exact identity

\[
 E_K={N_R\over U_R2^R3^{M_R}},\qquad 3\nmid U_R2^R,     \tag{16}
\]

and hence

\[
 \boxed{v_3(E_K)=v_3(N_R)-M_R,qquad
 v_3(Q_K)=\max(0,M_R-v_3(N_R)).}                        \tag{17}
\]

Formula (17), rather than a guessed endpoint rule, is necessary: multiple
top layers sometimes cancel modulo 3.

There is a clean infinite subsequence. Let

\[
 R=3^e,\qquad e\ge1\text{ odd},\qquad K=(R-3)/4.       \tag{18}
\]

The endpoint has \(r+v_3(r)=R+e\). Every earlier odd \(r\le R-2\) has
\(v_3(r)\le e-1\), and thus \(r+v_3(r)\le R+e-3\). The endpoint is the
unique three-adic minimum; moreover \(3\nmid(3^R+2^R)\). Therefore

\[
 \boxed{v_3(E_K)=-(R+e),\qquad v_3(Q_K)=R+e}            \tag{19}
\]

on (18). By LTE,

\[
 v_3(10^t-1)=2+v_3(t),
\]

so the exact order of \(10\) modulo \(3^b\), \(b\ge2\), is \(3^{b-2}\).
On (18), the three-primary coordinate alone consequently has complete
period

\[
 3^{R+e-2}.                                             \tag{20}
\]

This enormous period is arithmetically real and completely unusable for
bracket transfer because of (13).

## 5. The exact multiband local law

Let \(p>3\) be prime with \(\sqrt R<p\le R\), and let

\[
 m_p=\max\{m\le R/p:m\text{ odd}\}.                    \tag{21}
\]

Define the nonzero rational partial constant

\[
 C_M=4\sum_{m\le M,\ m\ {\rm odd}}
 {\chi_4(m)\over m}\left({1\over2^m}+{1\over3^m}\right).
                                                                    \tag{22}
\]

This rational is positive: pairing exponents \(4a+1,4a+3\) leaves a
positive difference for each base \(2,3\), and an unmatched term, when
present, is positive.

Only exponents \(r=mp\) contribute to \(pE_K\pmod p\). Since
\(\chi_4(mp)=\chi_4(p)\chi_4(m)\), and Fermat gives
\(q^{-mp}\equiv q^{-m}\pmod p\) for \(q=2,3\), their sum is

\[
 \boxed{pE_K\equiv\chi_4(p)C_{m_p}\pmod p.}            \tag{23}
\]

Here a rational with \(p\)-unit denominator is interpreted in
\(\mathbb F_p\). Every nonsingular term vanishes after multiplication by
\(p\). It follows immediately that

\[
 p\nmid\operatorname{num}(C_{m_p})
 \quad\Longrightarrow\quad
 v_p(E_K)=-1.                                           \tag{24}
\]

Thus \(p\) occurs exactly once in \(Q_K\). At every decimal shift \(j\), the
local prefix law is

\[
 p10^jE_K\equiv10^j\chi_4(p)C_{m_p}\pmod p.            \tag{25}
\]

Equivalently, if \(Q_K=pD\), then the actual reduced numerator obeys

\[
 P_KD^{-1}\equiv\chi_4(p)C_{m_p}\pmod p.               \tag{26}
\]

For the first band \(R/3<p\le R\), one has \(m_p=1\) and

\[
 C_1={10\over3}.                                       \tag{27}
\]

Apart from the fixed cancellation prime \(5\), all sufficiently large
primes in this band therefore survive exactly once. Its product alone has

\[
 \log_{10}\prod_{R/3<p\le R}p
 ={2R\over3\log 10}+o(R)
 =0.289529\ldots R+o(R),                               \tag{28}
\]

which is just below the leading prefix scale (6). The lower bands are what
push the radical past that scale.

## 6. Radical asymptotic from fixed bands

Fix an odd integer \(L\ge3\). For \(R>L^2\), every prime
\(p\in(R/L,R]\) satisfies \(p^2>R\), and (21) takes one of the finitely many
odd values \(1,3,\ldots,L\). Each \(C_M\) in that finite list is a fixed
nonzero rational. Once \(R\) is large enough, \(p\) exceeds every prime
dividing their numerators and denominators. Equations (23)--(24) then show
that every prime in \((R/L,R]\) occurs exactly once in \(Q_K\).

Let

\[
 \operatorname{rad}_{(6)}(Q)
 =\prod_{p\mid Q,\ p\nmid6}p.
\]

Every prime other than \(2,3\) in the natural denominator of (3) is at most
\(R\).
Consequently

\[
 \vartheta(R)-\vartheta(R/L)+O_L(1)
 \le\log\operatorname{rad}_{(6)}(Q_K)
 \le\vartheta(R)+O(1).                                 \tag{29}
\]

The prime number theorem in the form \(\vartheta(x)\sim x\) gives

\[
 \liminf_{K\to\infty}{\log\operatorname{rad}_{(6)}(Q_K)\over R}
 \ge1-{1\over L}.
\]

Letting the fixed \(L\) tend to infinity and using the upper bound in (29)
proves (2). This fixed-\(L\)-then-\(R\) order is important: no uniform claim
about the prime divisors of all growing \(C_M\) is being made.

For later scale notation, take the explicit certified product

\[
 G_K^*=\prod_{\substack{\sqrt R<p\le R,\ p>3\\
              p\nmid\operatorname{num}(C_{m_p})}}p.    \tag{29a}
\]

Every factor of \(G_K^*\) occurs exactly once in \(Q_K\). The same fixed-band
lower bound and the upper bound \(G_K^*\mid\operatorname{rad}_{(6)}(Q_K)\)
give \(\log G_K^*=R+o(R)\). This conclusion still uses the two-stage
fixed-\(L\) argument; it is not a uniform estimate for a growing local
constant.

## 7. What the global CRT coordinate does and does not give

Choose any finite set \(\mathcal P\) of primes certified by (24), and put

\[
 G=\prod_{p\in\mathcal P}p,\qquad Q_K=GC.
\]

The exponent-one result makes \((G,C)=1\). For each selected \(p\), (26)
is equivalent to

\[
 P_K\equiv C\,\chi_4(p)C_{m_p}{G\over p}\pmod p.       \tag{30}
\]

Hence CRT determines a unique \(S\pmod G\) with

\[
 S\equiv\chi_4(p)C_{m_p}{G\over p}\pmod p,
 \qquad P_KC^{-1}\equiv S\pmod G.                      \tag{31}
\]

This is an exact selected-numerator projection, not a random-numerator
model. Writing \(e_m(x)=\exp(2\pi i x/m)\), additive CRT factors its
exponential phase as

\[
 e_{Q_K}(P_K10^j)
 =e_G(P_KC^{-1}10^j)\,e_C(P_KG^{-1}10^j).              \tag{32}
\]

Equation (31) explicitly determines the first factor. It supplies no bound
for (32), because the second factor uses the same exponent \(j\) and can be
perfectly correlated with the first. A real interval modulo \(GC\) is not a
Cartesian product of intervals modulo \(G\) and \(C\). In particular, the
complement contains the entire dyadic transient \(2^{R-2}\).

This is the missing step in the naive “large radical plus CRT” argument:
one must control the **joint actual phase**, not merely all its selected
prime projections.

There is also a sharp denominator-only counterexample. Keep the exact same
denominator \(Q_K\), but choose the legal reduced numerator \(a=1\). From
(2), (6), and (9),

\[
 {10^{J_{K,\ell}}\over Q_K}
 \le\exp(-R+o(R)).                                      \tag{33}
\]

Thus every point \(10^j/Q_K\), \(0\le j\le J_{K,\ell}\), lies in an
asymptotically vanishing neighborhood of zero. No theorem uniform over
reduced numerators can produce the needed cylinder coverage from the
denominator, radical, order, or lifting data alone. This counterexample does
not obey (31), so a successful theorem would have to exploit the actual
selected numerator and its complementary coordinate.

## 8. Why complete-period and known short-sum tools do not close the gap

After \(A_K=R-2\) shifts, all factors common with base 10 have disappeared
and the remaining rational states form a multiplicative orbit modulo a
denominator coprime to 10. Equation (13) says none of those states transfers
through the pi bracket. Even perfect distribution of the complete period
would therefore prove nothing about a pi cylinder.

Before \(A_K\), the two-primary modulus shrinks at every step. Taking
\(G=G_K^*\) from (29a), factoring the dyadic part away leaves an odd CRT
projection of length

\[
 N=J_{K,\ell}+1=\Theta(R)=\Theta(\log G),               \tag{34}
\]

but the full state still contains its correlated shrinking dyadic
coordinate. The corresponding odd-component sums are Korobov-type sums

\[
 \sum_{j<N}e_M(a10^j),                                  \tag{35}
\]

at logarithmic length. The bounded literature search found no theorem in
this regime for the actual coefficient:

* Vandehey's fixed-prime-support bounds require a superlogarithmic length,
  and their fixed-support hypothesis fails outright by (2);
* the quoted general Bourgain bounds require \(N>M^\gamma\) for a positive
  parameter, exponentially beyond (34);
* complete subgroup or complete-period estimates concern exponentially
  many states, not this ordered prefix and not its dyadic correlation.

The scale comparison does not prove that every conceivable transient method
must fail. It proves that the standard CRT projection, complete-period, and
available short-exponential-sum inputs do not imply the needed hit.

## 9. The remaining transient statement is V1 in bracket form

For a target cylinder \(I_{\ell,c}\), a sufficient statement is

\[
 \exists K\ \exists 0\le j\le J_{K,\ell}:
 [10^jE_K,10^jU_K]
 \text{ lies inside a translate of }I_{\ell,c}.         \tag{36}
\]

If (36) holds, pi has the word. Conversely, suppose pi has that word at a
fixed position \(j\). Irrationality places \(10^j\pi\) strictly away from
the two rational cylinder boundaries. Since \(E_K,U_K\to\pi\), all
sufficiently large \(K\) have their scaled bracket inside the same cylinder;
also \(J_{K,\ell}\to\infty\). Thus (36), quantified over every word, is
equivalent to V1.

More precisely, the stronger demand

\[
 {1\over J_{K,\ell}+1}
 \sum_{j=0}^{J_{K,\ell}}e^{2\pi i h10^jE_K}\longrightarrow0
 \quad(h\in\mathbb Z\setminus\{0\})                   \tag{37}
\]

for one (hence every) fixed \(\ell\), once \(J_{K,\ell}\ge0\), is equivalent
to base-10 normality of pi. Indeed, the geometric sum of the phase errors
between \(E_K\) and pi is \(O_h(1)\) across this horizon, while its length is
\(\Theta(R)\); the successive horizon lengths have bounded gaps; and Weyl's
criterion applies. Thus demanding (37), rather than one cylinder hit, would
silently strengthen V1 to normality.

Therefore the exact missing theorem is not “show that the radical is large”
or “wait for a full period.” It is a pi-specific joint-CRT localization
theorem for the selected numerator during \(0\le j<R-2\). No such theorem
was found, and merely asserting it would restate the target.

## 10. Exact replay

The companion checker is
[`euler_two_three_check.py`](euler_two_three_check.py). It uses Python
integers and `Fraction` arithmetic for every assertion. Run it from the
repository root:

```text
python3 work/ultrapi-resume/euler_two_three_check.py
```

The 2026-08-12 replay checked 121 exact brackets, exact two- and
three-primary certificates and preperiods, 9,265 local congruences, 9,170
nonzero local valuation cases, 9,170 recombined selected-prime CRT
coordinates, and the exact three-primary subsequence at \(R=3,27,243\).
Its final line was:

```text
all exact checks passed
```

These finite checks are `experiment`, not a proof of an asymptotic or of
V1. They are designed to falsify sign, endpoint, cancellation, and CRT
normalization errors in the displayed formulas.

## 11. Literature and repository search log

| Date (UTC) | Primary source or repository query | Finding used |
|---|---|---|
| 2026-08-12 | Mathlib `Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean`, local theorem search | `Real.arctan_inv_2_add_arctan_inv_3` proves (1); no digit-distribution consequence is bundled with it. |
| 2026-08-12 | Jack S. Calcut, [*Gaussian Integers and Arctangent Identities for pi*](https://isis2.cc.oberlin.edu/faculty/jcalcut/gausspi.pdf), Amer. Math. Monthly 116 (2009), 515--530; retrieved PDF SHA-256 `d650da61527c78c67caca06758363280bac7303cb2b553fc786914ddf3a4886f` | Records (1), its Gregory-series use, and attributes it to Machin (1706). It makes no V1 or normality claim. |
| 2026-08-12 | Joseph Vandehey, [*Differencing Methods for Korobov-type Exponential Sums*](https://arxiv.org/abs/1606.07911); retrieved PDF SHA-256 `28f10a84ee2038d09af33f1509e74386d70c96baee158143b0924c80e3cc1b7c` | Theorems 1.4 and 7.2 cover fixed finite prime support at superlogarithmic lengths; Section 2 records the classical, prime-power, and Bourgain ranges. |
| 2026-08-12 | Bourgain, [*The sum-product theorem in \(\mathbb Z_q\) with \(q\) arbitrary*](https://doi.org/10.1007/s11854-008-0044-2) | General nontrivial bounds used in Vandehey's comparison require a positive-power length/order regime, not (34). |
| 2026-08-12 | Pierre Dusart, [*Estimates of \(\psi,\theta\) for large values of \(x\) without the Riemann hypothesis*](https://www.ams.org/journals/mcom/2016-85-298/S0025-5718-2015-03005-1/) | Records the unconditional prime-number-theorem consequence \(\vartheta(x)\sim x\) used in (29). |
| 2026-08-12 | Local search of `ultrapi.md`, `work/ultrapi-resume/`, `TheoryLib/`, and Mathlib for `arctan(1/2)`, `arctan(1/3)`, Hutton, CRT, radical, and Korobov infrastructure | The Hutton bracket, multiband denominator, global CRT, and logarithmic-prefix audits provide the closest infrastructure; no existing (2/3)-shadow transient-localization theorem was found. |

This is a bounded dated search, not a novelty claim.

## Bottom line

The \(1/2+1/3\) shadow improves the denominator radical away from \(2,3\)
all the way to
\(\exp(R+o(R))\) and supplies explicit actual-numerator residues in every
fixed prime band. But its exact two-primary denominator exponent is \(R-2\),
more than three times its transferable prefix in the leading scale. The
complete rational orbit begins only after the pi bracket has become useless.
Before then, CRT leaves a correlated shrinking dyadic coordinate, and known
short-orbit estimates are outside the logarithmic regime. The route reduces
to the unproved selected-numerator transient hit (36), which is equivalent
to V1 when required for every word.
