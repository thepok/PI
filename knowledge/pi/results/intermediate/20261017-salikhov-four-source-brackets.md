# Four-source positive Salikhov mixtures: both sides with surviving prime precision

Date: 2026-10-17. Labels: `proof sketch` and exact `experiment`.
No Lean verification, novelty claim, or decimal-occurrence conclusion.

## Result

Use the modified Salikhov normalization

\[
 I_j=a_j+b_j\pi,\qquad c_j=2^{2-\lfloor5j/2\rfloor}a_j,\quad
 q_j=2^{2-\lfloor5j/2\rfloor}b_j\in\mathbb Z_{>0},\qquad
 \mathcal L_j=c_j+q_j\pi.
\]

For every sufficiently large \(k\), the construction below gives two
reduced fractions, obtained using only positive integer mixing coefficients,

\[
 \frac{P_k^{\mathrm{lo}}}{Q_k^{\mathrm{lo}}}<\pi<
 \frac{P_k^{\mathrm{hi}}}{Q_k^{\mathrm{hi}}},\qquad Q_k^*>0,
\]

satisfying, for either endpoint,

\[
 \boxed{Q_k^*\text{ odd},\qquad v_5(Q_k^*)=k,}
 \tag{1}
\]

\[
 \boxed{v_2(P_k^*)\ge2r_k-11-\lfloor\log_2(4r_k+1)\rfloor,
 \quad \frac{31}{32}n_k<r_k\le\frac{63}{64}n_k,
 \quad n_k=\frac{5^k+1}{2},}
 \tag{2}
\]

and

\[
 \boxed{0<\left|\pi-\frac{P_k^*}{Q_k^*}\right|
       \le(Q_k^*)^{-13/12}.}
 \tag{3}
\]

Before reduction, the mixed multiplier has two-adic valuation at most 12.
The source indices are selected from the four-element set

\[
 \{r_k,r_k+1,r_k+30,r_k+31\}.
\]

Both signs are supplied near every sufficiently large five-adic index.
There is no assumption about distribution of the recurrence phase along
powers of two or five. The theorem is eventual; the inherited asymptotic
does not here supply an effective universal cutoff.

## Inputs and normalization

The exact integral and recurrence are from
[Zeilberger--Zudilin, Part II](https://arxiv.org/html/1912.06345v2) and their
[published recurrence output](https://sites.math.rutgers.edu/~zeilberg/tokhniot/oSALIKHOVpi3.txt).
The latter uses \(-I_j/5\); its homogeneous recurrence is unchanged, but
its initial conditions must be multiplied by \(-5\).

The source and preceding repository proof sketches supply:

* At \(n_k=(5^k+1)/2\), the companion-survival theorem gives
  \(v_5(q_{n_k})=k\), \(v_5(c_{n_k})=0\).
* Every \(j\ge1\) satisfies
  \[
  v_2(c_j)\ge H_j:=2j+1-\lfloor\log_2(4j+1)\rfloor,
  \quad v_5(c_j)\ge-\lfloor\log_5(4j)\rfloor.
  \]
  The rational denominator of \(c_j\) divides the odd part of
  \(\operatorname{lcm}(1,\ldots,4j)\).
* The actual-integral asymptotic is
  \[
  I_j=j^{-1/2}\left(A\alpha^j+\overline A\overline\alpha^j
                    +O(\rho^j/j)\right),\qquad A\ne0,
  \tag{4}
  \]
  where \(\alpha=\rho e^{i\theta}\) is the upper-half-plane small
  root of
  \[
  \chi(X)=108X^3-2359989X^2+138304X-2048.
  \]
  Its large root \(\Lambda\) satisfies \(21000<\Lambda<22000\),
  \(\rho^2=2048/(108\Lambda)\), and
  \(\log q_j=Bj+o(j)\), where
  \(B=\log\Lambda-\tfrac52\log2>0\).
* The actual multipliers are positive and strictly increasing. The source
  recurrence proves \(b_{j+1}>10000b_j\) for \(j\ge1\). Therefore
  \(q_{j+1}>1250q_j\), so strict increase persists after the
  parity-dependent power-of-two normalization.

These are the established inputs from the
[local-pair](20260906-salikhov-mod5-support.md),
[companion-survival](20261017-salikhov-companion-survival.md),
[odd-multiplier](20261017-salikhov-odd-multiplier.md), and
[mixed-precision](20261017-salikhov-mixed-precision.md) notes. In particular, (4) is an
actual-pi connection statement, not an asymptotic for an arbitrary
replacement constant. The new work below is the fixed-shift congruence and
its uniform four-source sign application.

## 1. Fixed shifts inherit the binary multiplier

For \(N=2^Lm\), \(L\ge8\), \(m\ge1\), and every \(0\le s\le63\),

\[
 \boxed{q_{N+s}\equiv q_s\binom N{N/4}\pmod{2^{L-5}}.}
 \tag{5}
\]

Here \(q_0=1\); \(m\) need not be odd. If \(e=s_2(3m)\), factorial
valuations give \(v_2\binom N{N/4}=e\). Thus

\[
 e+v_2(q_s)<L-5\quad\Longrightarrow\quad
 v_2(q_{N+s})=e+v_2(q_s).
 \tag{6}
\]

Only the four fixed values

| Shift \(s\) | 0 | 1 | 30 | 31 |
|---|---:|---:|---:|---:|
| \(v_2(q_s)\) | 0 | 2 | 2 | 2 |

are needed in the application. They are checked independently by the exact
published recurrence and direct integer coefficient extraction.

### Proof of the shift congruence

In \(\mathbb Z_2[\tau]\), \(\tau^2=2\), write

\[
 h(z)=1-7\tau z+39z^2-50\tau z^3+50z^4,\qquad
 U(z)=\frac{(1-2\tau z)^2h(z)^2}{(1-\tau z)^3}.
\]

The source extraction, valid at every nonnegative index, is

\[
 q_n=(-1)^n\tau^{n\bmod2}[z^{3n}]\frac{U(z)^n}{1-\tau z}.
 \tag{7}
\]

The preceding ramified argument gives
\(U\equiv(1+z^4)(1+\tau z)\pmod2\), hence
\(U^N\equiv(1+z^4)^N(1+\tau z)^N\pmod{2^{L+1}}\).
Also \((1+\tau z)^N\equiv1\pmod{2^L}\), because its \(j\)-th
coefficient has valuation at least \(L-v_2(j)+j/2\ge L\).
Keep \(U^s\) outside this lift. The parity of the extracted coefficient
and the factor \(\tau^{s\bmod2}\) make the error a rational two-adic
integer divisible by \(2^L\).

Set \(R=3N/4\) and

\[
 H_{s,\ell}=(-1)^s\tau^{s\bmod2}[z^{3s+4\ell}]
                          \frac{U(z)^s}{1-\tau z}.
\]

Then

\[
 q_{N+s}\equiv
 \sum_{\ell=-\lfloor3s/4\rfloor}^{R}
 H_{s,\ell}\binom N{R-\ell}\pmod{2^L},
 \qquad H_{s,0}=q_s.
 \tag{8}
\]

Out-of-support binomial coefficients vanish. With
\(J(y)=2-14y+39y^2-50y^3+25y^4\), substitution \(y=\tau z\) gives

\[
 H_{s,\ell}=(-1)^s2^{2\ell-\lfloor s/2\rfloor}
 [y^{3s+4\ell}]
 \frac{(1-2y)^{2s}J(y)^{2s}}{(1-y)^{3s+1}}.
\]

The displayed coefficient is integral, and the original ramified formula
independently gives two-adic integrality. Consequently

\[
 v_2(H_{s,\ell})\ge\max\{0,2\ell-31\}.
 \tag{9}
\]

For nonzero \(|\ell|<2^{L-2}\), \(v_2(R-\ell)=v_2(\ell)\), so
\(v_2\binom N{R-\ell}\ge L-v_2(\ell)\).
Negative shifts range only from \(-47\) to \(-1\), giving
\(v_2(\ell)\le5\) and total order at least \(L-5\).
For \(1\le\ell\le31\), the total order is at least \(L-4\).
For \(32\le\ell<2^{L-2}\), the bound
\(2\ell-31\ge\ell\ge v_2(\ell)\) gives total order at least \(L\).
Finally, positive \(\ell\ge2^{L-2}\) have order at least
\(2^{L-1}-31\ge L-5\) directly from (9). There are no larger negative
shifts when \(L\ge8\). Every nonzero shift in (8) therefore vanishes
modulo \(2^{L-5}\), proving (5).

## 2. Four fixed phase offsets force both signs

The exact algebraic root certificate gives

\[
 0<\theta<\pi/2,\qquad
 (51/500)^2<\sin^2\theta<11/1000.
\]

For transparency, if \(S=2359989/108\) and \(P=2048/108\), then
\(\cos^2\theta=\Lambda(S-\Lambda)^2/(4P)\). Rational bisection in
the increasing interval \(21851<\Lambda<21852\) proves the stated
bounds without evaluating a floating-point phase. Since
\(\sin\theta<\theta<\tan\theta\) and
\(11/989<(53/500)^2\),

\[
 \frac{51}{500}<\theta<\frac{53}{500}.
\]

The angles \(0,\theta,30\theta,31\theta\) lie in this order before
\(2\pi\). Their circular gaps are
\(\theta,29\theta,\theta,2\pi-31\theta\). Each is less than
\(\pi-1/100\), as follows from \(31/10<\pi<22/7\) and

\[
 \frac{31}{10}-\frac{53}{500}>\frac1{100},\quad
 \frac{31}{10}-\frac{29\cdot53}{500}>\frac1{100},\quad
 \frac{31\cdot51}{500}-\frac{22}{7}>\frac1{100}.
\]

After any translation, the nearest point to zero is within
\(\pi/2-1/200\), and the nearest point to pi has the same bound.
Their cosines are respectively greater than \(\sin(1/200)>1/400\)
and less than \(-1/400\). The inequality
\(\sin x\ge2x/\pi\), \(0\le x\le\pi/2\), and \(\pi<4\)
give the last explicit margin.

Put \(\beta=\rho/2^{5/2}\in(0,1)\), \(C=-\log\beta\), and
\(\varphi=\arg A\). Formula (4) becomes

\[
 \mathcal L_j=2^{2+(j\bmod2)/2}j^{-1/2}\beta^j
 \bigl(2|A|\cos(j\theta+\varphi)+O(1/j)\bigr).
 \tag{10}
\]

The remainder is uniform on four fixed shifts. There are therefore fixed
constants \(d,D>0\) such that, for every sufficiently large \(r\),
the set \(r+\{0,1,30,31\}\) contains \(j_+,j_-\) with

\[
 \mathcal L_{j_+}\ge dr^{-1/2}\beta^r,
 \qquad\mathcal L_{j_-}\le-dr^{-1/2}\beta^r,
 \qquad |\mathcal L_t|\le Dt^{-1/2}\beta^t.
 \tag{11}
\]

The fixed factor \(\beta^{31}\) is absorbed into \(d\). One may select
the maximum and minimum actual linear errors over the four sources.
Rational enclosures for pi decide all comparisons: a tie between distinct
forms would make pi rational because their multipliers are distinct.
The selection needs no unknown connection phase.

## 3. The nearby grid and the two positive mixtures

For \(n=n_k\), set

\[
 L=\lfloor\log_2n\rfloor-7,\qquad
 m=\max\{u>0:u\text{ odd},\ u\le63n/(64\cdot2^L)\},\quad r=2^Lm.
 \tag{12}
\]

For \(k\ge11\), \(L\ge17\), \(125\le m\le251\), and
\(e=s_2(3m)\le9\). Rounding down to the preceding odd multiplier loses
less than \(2^{L+1}\le n/64\), giving
\(31n/32<r\le63n/64\). Also \(r+31\le127n/128<n\).
Equations (5)--(6) give exact orders

\[
 v_2(q_{r+s})=e+v_2(q_s)\le11,
 \qquad s\in\{0,1,30,31\}.
 \tag{13}
\]

For either source \(j=j_+\) or \(j_-\) selected in (11), put
\(T_j=5^{k+\lfloor\log_5(4j)\rfloor+1}\), \(e_j=v_2(q_j)\), and
choose \(\lambda_j=1\) if
\(q_n+T_jq_j\not\equiv0\pmod{2^{e_j+2}}\); otherwise choose 3.
The two candidates differ by \(2T_jq_j\), of exact order \(e_j+1\).
Thus the positive mixture

\[
 q_j^*=q_n+\lambda_jT_jq_j>0,\qquad
 c_j^*=c_n+\lambda_jT_jc_j
 \tag{14}
\]

satisfies \(v_2(q_j^*)\le e_j+1\le12\).
At five, the perturbation to \(q_n\) has order greater than \(k\),
and that to \(c_n\) has order at least \(k+1\). Hence
\(v_5(q_j^*)=k\), \(v_5(c_j^*)=0\). At two,
\(v_2(c_j^*)\ge H_r\), because \(H_t\) is increasing.
Reduction of \(-c_j^*/q_j^*\) therefore proves (1)--(2).

The coefficient obeys \(3T_j<120nj=O(n^2)\). Since \(n-j\ge n/128\),
\(T_jq_j=o(q_n)\). Equation (11) and \(n-r\ge n/64\) also give
\(|\mathcal L_n|=o(T_j|\mathcal L_j|)\), for both selected sources.
Consequently the mixed linear errors inherit their respective positive
and negative signs. Dividing by the positive multipliers proves the claimed
strict bracket around pi.

## 4. Common denominator and approximation rate

The common denominator
\(D_n=\operatorname{oddpart}(\operatorname{lcm}(1,\ldots,4n))\)
clears every selected rational companion. The prime number theorem gives
\(\log D_n\le4n+o(n)\), hence

\[
 Q_k^*\le D_nq_j^*\le\exp[(B+4)n+o(n)].
 \tag{15}
\]

Using the signed linear forms before division, rather than discarding the
small multiplier weight, gives

\[
 |\pi-P_k^*/Q_k^*|
 \le\exp[-Bn-Cr+o(n)]
 \le\exp[-(B+31C/32)n+o(n)].
 \tag{16}
\]

The root product gives
\(C=\tfrac12\log\Lambda-2\log2+\tfrac32\log3\).
The strict comparison
\(B+31C/32>\tfrac{13}{12}(B+4)\) is equivalent to
\(\Lambda^{77}3^{279}>2^{332}e^{832}\).
It follows from \(\Lambda>21000\), \(e<11/4\), and

\[
 \boxed{21000^{77}3^{279}4^{832}>2^{332}11^{832}.}
\]

The exact checker verifies this integer inequality. The strict gap absorbs
the \(o(n)\) terms in (15)--(16), proving (3). Exact five-adic orders make
both reduced denominator sequences unbounded.

## Scope, avoider, and exact experiment

The actual-pi input enters in (4) and (11). Replacing pi by \(4/9\) in
the same rational source pairs introduces the nonzero large mode
\(q_j(4/9-\pi)\). All sufficiently late replacement errors are negative,
so the four-source two-sign premise fails for this explicit word-avoider.
The checker also verifies that all of its mixed rational numbers exceed
\(4/9\), while they occur on both sides of pi.

The theorem controls the approximation direction and surviving prime
orders together. It does not control a prescribed ordered residue. Writing
\(Q_k^*=5^kQ'_k\) leaves \(Q'_k\) coprime to ten; the residues after
decimal shifting modulo this remaining factor are unspecified. A bracket
certifies a prescribed decimal cylinder when its scaled ordered interval
lies in one appropriate integer translate of that cylinder, with endpoints
and wraparound treated correctly. No theorem here places these brackets
in an arbitrary preassigned cylinder at unbounded horizons. No E, CW0,
CW9, or V1 conclusion is claimed.

The width 31 refers to the four selected sources within each admissible
dyadic block. There is no claim that admissible blocks have bounded gaps
among all positive integers. Earlier sign-population results on good
dyadic powers are not used.

The motivating adjacent-pair observation is shorter: nonreal conjugate
phases make at least one of two consecutive errors nonnegligible, and
positive and negative perturbations give both approximation directions.
The fixed-shift lemma above improves that observation by giving positive
coefficients throughout, with the same prime-precision bounds.

[`four_source_audit.py`](../../../../workflows/experiments/salikhov_signed_block_20261017/four_source_audit.py)
produces the tracked [finite certificate](../../../../workflows/experiments/salikhov_signed_block_20261017/four_source_certificate.json). It verifies
the fixed-shift congruence with a separate finite-precision root-coordinate
evaluator, checks the needed fixed coefficients directly against the
published recurrence, and proves the algebraic four-point gap and rate
inequalities. Literal large-grid checks only concern arithmetic, and do
not pretend to evaluate actual pi signs at those indices.

Its finite actual-pi examples use \((k,n,r)=(3,63,16),(4,313,256),
(5,1563,1472)\), with individually verified binary orders. These are
specified finite auxiliary choices, not the eventual grid (12). All six
positive mixtures have the claimed prime orders and bracket pi. Both
\(k=5\) endpoints satisfy the literal \(13/12\) rate; only one at
\(k=4\) does, and neither at \(k=3\) does. These early failures are
recorded explicitly and do not determine an effective asymptotic cutoff.

## Appendix A. An irrational word-avoider with stronger two-sided data

The constant replacement above tests the particular source mechanism.
The following independent construction shows that even an irrational
word-avoider can satisfy stronger abstract approximation and prime-order
data on both sides. Its label is `proof sketch`; its finite certificate
is a separate exact `experiment`.

Let \(\xi=\sum_{j\ge1}t_j10^{-j}\), where \(t_j\) is the parity
of the binary digit sum of \(j\). It avoids the digit 2. The
[Bugeaud theorem](https://aif.centre-mersenne.org/articles/10.5802/aif.2666/)
gives \(\mu(\xi)=2\). For every \(k\ge1\) and every prescribed
integer \(F\ge0\), there are reduced fractions on both sides,

\[
 P^-/Q^-<\xi<P^+/Q^+,
\]

such that both denominators are odd, \(v_5(Q^\pm)=k\),
\(v_2(P^\pm)\ge F\), \(v_2(P^\pm)\ge\tfrac14\log_2Q^\pm\),
and

\[
 0<|\xi-P^\pm/Q^\pm|\le(Q^\pm)^{-6/5}.
\]

This is an abstract-data separator. It does not satisfy the Salikhov
recurrence, its actual-pi connection constant, or its source-index
asymptotics. It prevents an inference from two-sided approximation and
these prime orders alone to decimal-word occurrence.

### Proof of the separator

Write consecutive convergents as \(p_-/q_-\), \(p/q\), and
\(p_+/q_+\). Exponent two implies, at all sufficiently late indices,

\[
q_-\ge q^{99/100},\qquad q_+\le q^{101/100}.
\tag{S1}
\]

Indeed the eventual lower bound with exponent \(201/100\), combined
with \(|\xi-p/q|<1/(qq_+)\), gives the second inequality. Applying
it one index earlier gives \(q_-\ge q^{100/101}>q^{99/100}\).
Take such an index with

\[
q\ge\max\{5^{100(k+1)},2^{200},2^{2F}\}.
\]

Set \(H=\lfloor\tfrac12\log_2q\rfloor\) and
\(M=2^H5^{k+1}\le q^{51/100}\). Unimodularity of the two
convergent columns gives unique coefficient residues modulo \(M\)
which enforce

\[
ap+bp_-\equiv0\pmod{2^H},\quad ap+bp_-\equiv1\pmod{5^{k+1}},
\]
\[
aq+bq_-\equiv1\pmod{2^H},\quad aq+bq_-\equiv5^k\pmod{5^{k+1}}.
\tag{S2}
\]

Choose representatives \(1\le a_0,b_0\le M\). Let
\(\delta=q\xi-p\) and \(\delta_-=q_-\xi-p_-\). These have
opposite signs. Standard continued-fraction error identities give

\[
0<|\delta|<|\delta_-|,\qquad
\frac{|\delta_-|}{|\delta|}<\frac{q_++q}{q}.
\tag{S3}
\]

The ratio bound follows from
\(|\delta_-|<1/q\) and \(|\delta|>1/(q_++q)\).

For the sign of \(\delta\), use

\[
a=a_0+hM,\quad b=b_0,\qquad h=\lceil q_+/q\rceil+2.
\]

Then \(a/b>h>|\delta_-|/|\delta|\). For the opposite sign,
use \(a=a_0\), \(b=b_0+M\); now \(b>a\) and
\(|\delta_-|>|\delta|\). Thus the two linear combinations have
opposite nonzero errors, and both use positive coefficients. Adding
multiples of \(M\) preserves (S2).

The coefficients in both constructions satisfy
\(a,b\le5Mq^{1/100}\). Their unreduced denominators are bounded by

\[
Q_{\rm raw}\le10q^{152/100}\le q^{31/20},
\tag{S4}
\]

where the last inequality follows from \(q\ge2^{200}\).
Both rational mixtures lie between the two convergents, so (S1) gives

\[
|\xi-P/Q|<\frac1{qq_-}\le q^{-199/100}
\le Q^{-6/5};
\]

the last step uses \((31/20)(6/5)=186/100<199/100\) and
\(Q\le Q_{\rm raw}\). By (S2), the common factor cancelled in
reduction is prime to 10. Hence \(Q\) is odd, \(v_5(Q)=k\), and
\(v_2(P)\ge H\ge F\). Finally

\[
H\ge\tfrac12\log_2q-1\ge\tfrac14\log_2Q
\]

by (S4) and \(q\ge2^{200}\). This proves all assertions.

The choice \(F=2n_k\) can match the literal source-index numerator
lower bound of the Salikhov theorem. It requires later convergents;
it does not reproduce the Salikhov relation between approximation error
and \(n_k\).

The accompanying
[`two_sided_separator.py`](../../../../workflows/experiments/salikhov_signed_block_20261017/two_sided_separator.py)
computes certified rational
bounds from 1,024 Thue–Morse digits, extracts 1,020 common continued-fraction
terms, and constructs both signs for each of \(k=1,\ldots,5\) with
requested numerator depth \(F=200\). All ten reduced fractions pass
the exact five-adic order, odd denominator, numerator depth, and literal
\(6/5\) rate checks. An independent rerun reproduces these results.
This finite computation verifies the displayed instances; the all-parameter
statement uses Bugeaud’s irrationality-exponent theorem.

## Appendix B. Finite period and transfer-horizon comparison

This appendix concerns the first three fractions in the preceding
[mixed-precision construction](20261017-salikhov-mixed-precision.md),
at the pinned source commit
[`2f49f0370b2dc1c61488b96cb45a8b4353821c86`](https://github.com/thepok/PI/blob/2f49f0370b2dc1c61488b96cb45a8b4353821c86/workflows/experiments/salikhov_mixed_precision_20261017/mixed_branch.py).
They are separate from the six four-source examples above. The elementary
period identity has label `proof sketch`; all numerical instances have
label `experiment`.

Write one of these reduced fractions as \(R=P/Q\), where
\(Q=5^kD\), \(D>1\), and \(\gcd(D,10)=1\). Its decimal preperiod
has length exactly \(k\), and its eventual period is

\[
L=\operatorname{ord}_D(10).
\]

The reduced denominator after \(h\) decimal shifts is exactly
\(Q/\gcd(Q,10^h)=5^{\max(k-h,0)}D\), which also proves that the
preperiod length \(k\) is minimal.
After \(k\) shifts, the remaining denominator is \(D\), and the
numerator \(2^kP\) is a unit modulo \(D\). A phase return after
\(h\) further shifts is therefore equivalent to
\(10^h\equiv1\pmod D\). For any known prime-power factors
\(p^a\mid D\), their orders of ten divide \(L\); their least common
multiple is a certified divisor of \(L\) even without factoring the
remaining cofactor.

The self-contained
[`period_gate.py`](../../../../workflows/experiments/salikhov_signed_block_20261017/period_gate.py)
reconstructs these rational fractions and bounds pi by exact
alternating-series enclosures in Machin's identity. It proves
\(10^{-E-1}<|R-\pi|<10^{-E}\) in each row:

| \(k\) | Source indices \((n,r)\) | Side of pi | \(E\) | Certified period information |
|---:|---|---|---:|---|
| 1 | (3,4) | below | 22 | \(L>24\), by direct modular iteration |
| 2 | (13,16) | above | 89 | \(14\,902\,327\,440\mid L\) |
| 3 | (63,64) | below | 374 | \(564\,601\,364\,960\,506\,035\,964\,401\,600\mid L\) |

Here \(E\) is the largest integer shift with scaled absolute error less
than one. It does not itself certify a shared digit: an intervening decimal
boundary may be closer than one. For these three fractions, a full-period
scan exceeds even that unit-error horizon. This is a finite limitation of
transferring a complete rational period using the absolute approximation
error. It proves no all-index order bound and excludes no other justified
transfer mechanism. In particular, it does not supply or rule out an
ordered target in a short initial segment of the rational orbit.

The [certificate](../../../../workflows/experiments/salikhov_signed_block_20261017/period_certificate.json)
records every found prime power, its exact order, and the remaining
unfactored cofactor. Euler exponents are reduced only after exact modular
power tests. Direct iteration also finds no return through
\(6\max(n,r)\) in any of the three cases.

## Reproduction and review

All three checkers use only the Python standard library and tracked inputs.
No pi digit file, floating-point phase, or external package is used. Run
from the repository root:

```sh
mkdir -p workflows/state/salikhov_signed_block_20261017
python3 workflows/experiments/salikhov_signed_block_20261017/four_source_audit.py --json workflows/state/salikhov_signed_block_20261017/four_source.json
cmp workflows/experiments/salikhov_signed_block_20261017/four_source_certificate.json workflows/state/salikhov_signed_block_20261017/four_source.json
python3 workflows/experiments/salikhov_signed_block_20261017/two_sided_separator.py --json workflows/state/salikhov_signed_block_20261017/separator.json
cmp workflows/experiments/salikhov_signed_block_20261017/separator_certificate.json workflows/state/salikhov_signed_block_20261017/separator.json
python3 workflows/experiments/salikhov_signed_block_20261017/period_gate.py > workflows/state/salikhov_signed_block_20261017/period.json
cmp workflows/experiments/salikhov_signed_block_20261017/period_certificate.json workflows/state/salikhov_signed_block_20261017/period.json
```

The default main certificate contains 64 independent fixed-coefficient
comparisons, 1,152 fixed-shift modular cases, 986 exact-valuation
conclusions within the available modulus, all 90 grids \(k=11,\ldots,100\),
and the six finite actual-pi mixtures. A separate review checked another
576 congruences directly from the published recurrence at \(L=8,9,10\),
including even multipliers and indices through 3135. Both the main proof
and Appendix A passed independent mathematical review. These reviews
are not a Lean verification.

Root reruns reproduced all three committed certificates byte for byte:

| Certificate | SHA-256 |
|---|---|
| Four-source mixtures | `7307c61667a1e8f27f27908ef29131cb593742ba100bfebb5d7bdd3bbe87adc4` |
| Two-sided separator | `9e9e3399fd0d8a078c9eefda2302a8c94f6d1a0c60b730b75b894ab48ba08d43` |
| Finite periods | `eb7f986f19d4b1bae24a1566280c3f4405cb3df9bf0438042d54055760dfb8b6` |
