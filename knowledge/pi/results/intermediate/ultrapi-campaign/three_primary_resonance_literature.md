# Nested 3-primary resonance: primary-literature audit

Audit date: **2026-08-12 UTC**

Search cutoff: **2026-08-12 UTC**

Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
Provenance: Marcel's immutable local question has no external source URL; none
is invented here.

## Outcome

No located theorem proves that every finite decimal word occurs in \(\pi\), or
proves the actual-shift resonance assertion isolated below. The canonical target
therefore remains a `conjecture`.

The useful outcome is a sharp applicability boundary. T52 supplies a
`machine-checked` nested 3-primary denominator, but every close theorem found
changes at least one indispensable quantifier or object: it averages over points,
chooses a multiplier, fixes the modulus, counts all bounded-height rationals,
studies an infinite invariant set, or follows a multiplicative orbit. None bounds
the one signed Fourier reconstruction at the actual moving Machin phase.

This bounded primary-source audit is `literature-checked` as of the search cutoff.
That label applies to the audit recorded here, not to the unresolved every-word
claim and not to a claim that the literature is exhausted.

**Single nearest theorem.** Maynard's Lemma 8.2 (restated as Lemma 10.1) is
the strongest located theorem aimed at the same kind of individual digital
Fourier coefficient. It would give exponential decay at a rational frequency
\(a/q+\eta\), but requires a factorization \(q=q_1q_2\) with
\((q_1,10)=1\) and \(q_1>1\). At an ASR frequency
\(\ell D_j/10^{n_j}\), the reduced denominator divides \(10^{n_j}\), so its
factor coprime to 10 is necessarily \(q_1=1\). The precise hypothesis fails
identically, not merely outside a known quantitative range.

## 1. Exact object being audited

The intended statement is about every **finite** decimal word. It cannot mean
that every infinite decimal sequence occurs as a tail of \(\pi\): there are only
countably many tail positions and uncountably many infinite sequences. Thus, for
nonempty \(w\in\{0,\ldots,9\}^m\), the target is

\[
 \exists n\ge 0:\quad
 (d_n(\pi),\ldots,d_{n+m-1}(\pi))=w.
\]

Fix such a word and let \(A_w(n)\subset\{0,\ldots,10^n-1\}\) be the
leading-zero-padded length-\(n\) strings avoiding \(w\), with
\(a_w(n)=|A_w(n)|\). Set

\[
 U_{w,n}=\bigcup_{k\in A_w(n)}[k/10^n,(k+1)/10^n).
\]

For the sampled Machin seed, write

\[
 x_j=\{10^jM_{3j}\}=\frac{b_j}{Q_j},\qquad
 Q_j=F_jD_j,\qquad b_j=F_jc_j+r_j,\qquad 0\le r_j<F_j,
\]

where \(D_j\) is the complete 3-primary part of the reduced denominator.
T52 proves the following `machine-checked` statement. If

\[
 3^{a_j}\le 12j+3<3^{a_j+1},
\]

then

\[
 v_3(10^jM_{3j})=1-a_j,\qquad D_j=3^{a_j-1},\qquad
 \frac{12j+3}{9}<D_j\le\frac{12j+3}{3}.                 \tag{1}
\]

Hence \(D_j=\Theta(j)\), while its exponent is only
\(a_j-1=\Theta(\log j)\). The abstract torsion groups
\(D_j^{-1}\mathbb Z/\mathbb Z\) are nested whenever the exponent increases.
The sampled **cosets** are not thereby nested: their translates

\[
 \alpha_j=\frac{r_j}{F_jD_j}
\]

change with \(j\), and T52 gives no compatibility relation between successive
\(\alpha_j\). Such compatibility would be new numerator information.

At the shadow length \(n_j=2j+m-1\), put \(M_j=10^{n_j}\). The exact sampled
count is

\[
 N_j=\sum_{c=0}^{D_j-1}
 \mathbf 1_{U_{w,n_j}}\!\left(\frac c{D_j}+\alpha_j\right).
\]

With \(e(t)=e^{2\pi it}\) and

\[
 S_{w,n}(h)=\sum_{k\in A_w(n)}e(-hk/10^n),
\]

the Poisson identity from
[`actual_shift_resonance_attack.md`](actual_shift_resonance_attack.md) is

\[
 N_j=Z_j+\mathcal R_j,\qquad
 Z_j=\frac{D_ja_w(n_j)}{10^{n_j}},                         \tag{2}
\]

\[
 \mathcal R_j=
 \lim_{H\to\infty}\sum_{0<|\ell|\le H}
 \frac{1-e(-\ell D_j/10^{n_j})}{2\pi i\ell}
 S_{w,n_j}(\ell D_j)e(\ell\theta_j),qquad
 \theta_j=\frac{r_j}{F_j}.                                \tag{3}
\]

The phase is not an auxiliary random translate. Exactly,

\[
 \theta_j=\{D_jx_j\},\qquad e(\ell\theta_j)=e(\ell D_jx_j). \tag{4}
\]

Equations (2)--(4) retain their existing `proof sketch` status: they are
elementary exact identities, but they have not been added to the verified Lean
track.

The theorem-sized sufficient assertion identified in the existing work is the
following `conjecture`:

\[
 \operatorname{ASR}(w):\quad
 \exists J_w\ \forall j\ge J_w:\qquad
 Z_j\le\frac14\quad\text{and}\quad |\mathcal R_j|\le\frac12. \tag{5}
\]

The first inequality follows from avoidance entropy and (1); the second is the
missing premise. Equations (2) and (5) give the integer \(0\le N_j\le3/4\), so
\(N_j=0\). Under the hypothesis that \(w\) is missing from \(\pi\), the valid
Machin shadow instead gives \(N_j\ge1\), a contradiction. The stronger
eventual statement (5) is not logically necessary: at one valid shadow scale,

\[
                         \mathcal R_j<1-Z_j                 \tag{6}
\]

would already force \(N_j=0\). No source below supplies (5) or (6).

### Quantifiers that must not be exchanged

The needed estimate is: fixed finite word \(w\); the actual deterministic seed
for each \(j\); the moving power \(D_j=3^{a_j-1}\asymp j\); the linked depth
\(n_j=2j+m-1\); and a signed bound at the one phase \(\theta_j\). It is not an
average over shifts, a statement for almost every point of a fractal, an
existence result for some \(10^s3^t\), a fixed-modulus residue theorem, or an
absolute-value average over Fourier frequencies.

## 2. Object mismatch in one view

| Route | Object actually controlled | Why it does not imply (5) |
|---|---|---|
| T52 | denominator valuation and \(D_j^{-1}\mathbb Z/\mathbb Z\) | no control of \(r_j/F_j\) or the signed sum (3) |
| Furstenberg/BLMV | multiplicative orbit \(\{10^s3^tx\}\) | ASR samples one additive coset and a sparse linked exponent slice |
| Host/Hochman--Shmerkin | \(\mu\)-almost every point for a positive-entropy invariant measure | the missing-word hypothesis does not make \(\pi\) a typical point |
| residue-class theorems | restricted-digit integers \(k\bmod 3^A\) | ASR samples Beatty positions \(\lfloor10^n(c/D+\alpha)\rfloor\), not one residue class |
| invariant-set intersections | infinite closed sets such as \(K_w\) | ASR uses the finite depth shadow \(U_{w,n}\); dimension zero is not emptiness |
| rational counting | all rationals in an infinite Cantor set up to height \(T\) | a Machin seed need only lie in \(U_{w,n}\), and a polynomial count is not zero |
| Fourier product bounds | ordinary coefficients away from base major aliases or averaged families | (3) lies exactly on a denominator dividing \(10^n\) and requires signed actual-phase cancellation |

## 3. Multiplicative \(\times10,\times3\) orbit theorems

### Furstenberg 1967: density, not the required slice

Primary source: H. Furstenberg,
[*Disjointness in Ergodic Theory, Minimal Sets, and a Problem in Diophantine
Approximation*](https://www.math.ucsd.edu/~asalehig/F_Disjointness.pdf),
Mathematical Systems Theory 1 (1967), 1--49,
[DOI 10.1007/BF01692494](https://doi.org/10.1007/BF01692494).

Exact locator: Section IV, Definition IV.1, Lemma IV.2, Proposition IV.2, and
Theorem IV.1 on printed page 48. Theorem IV.1 states that if \(\Sigma\) is a
non-lacunary multiplicative semigroup of integers and \(x\) is irrational,
then \(\Sigma x\) is dense in the circle. The paragraph on printed page 49
explicitly warns that equidistribution does not follow in this generality.

Substitution: \(\Sigma=\langle10,3\rangle\), \(x=\pi\). Since \(10\) and \(3\)
are multiplicatively independent and \(\pi\) is irrational,

\[
                       \{10^s3^t\pi:s,t\ge0\}
\]

is dense modulo one.

Applicability: this is a valid positive consequence, but it does not control the
curve of exponents generated by T52, where \(t=a_j-1\asymp\log j\) and the
decimal exponent is tied to \(j\) (and to a Fourier alias \(v\)). Density of the
union over all \((s,t)\) gives no discrepancy, rate, signed sum, or information
for the fixed \(t\)-slice appearing at a given seed.

### Bourgain--Lindenstrauss--Michel--Venkatesh 2009: effective existence

Primary source: J. Bourgain, E. Lindenstrauss, P. Michel, A. Venkatesh,
[*Some effective results for \(\times a\,\times b\)*](https://math.stanford.edu/~akshay/research/blmv.pdf),
Ergodic Theory and Dynamical Systems 29 (2009),
[DOI 10.1017/S0143385708000898](https://doi.org/10.1017/S0143385708000898).

Exact locators and substitutions:

* **Theorem 1.4 (printed page 2).** If
  \(H_\mu(\mathcal P_N)\ge\rho\log N\),
  \(100/\log_aN\le\delta\le\rho/20\), and \(f\ge0\) is \(C^1\), then there
  exists some \(m=a^sb^t<N\) for which the pushforward \(m.\mu\) has the
  displayed lower bound against \(f\). With \((a,b)=(10,3)\), the multiplier
  is chosen by the theorem. ASR prescribes \(D_j\), \(x_j\), and the actual
  phase, so the existential multiplier cannot be substituted into (3).
* **Corollary 1.6 (printed pages 2--3).** For
  \(S\subset N^{-1}\mathbb Z/\mathbb Z\), it assumes \((N,ab)=1\),
  \(|S|>N^\rho\), and again concludes that some semigroup multiplier works.
  Taking \(N=3^A\), \(a=10\), \(b=3\) violates \((N,ab)=1\) exactly.
* **Theorem 1.8 (printed page 3).** If \(x\) satisfies
  \(|x-p/q|\ge q^{-k}\) for some \(k\) and all \(q\ge2\), then
  \(\{a^sb^tx:s,t\le N\}\) is
  \((\log\log N)^{-\kappa_5}\)-dense. The current primary bound
  \(\mu(\pi)\le7.103205334137\ldots\), due to Zeilberger--Zudilin, lets one
  enlarge \(k\) to meet this hypothesis for \(x=\pi\). Thus the theorem really
  does apply to the full two-parameter \((10,3)\) orbit of \(\pi\). It still
  supplies neither equidistribution nor a bound on the linked slice
  \(t=a_j-1\), much less the weighted reconstruction (3).
* **Theorem 1.10 (printed page 3).** Its effective rational-orbit statement
  assumes \((ab,N)=1\). It is unavailable for the 3-primary denominator
  \(N=3^A\).

The irrationality-measure source used in the third substitution is D. Zeilberger
and W. Zudilin,
[*The Irrationality Measure of Pi is at most 7.103205334137...*](https://arxiv.org/abs/1912.06345),
Moscow Journal of Combinatorics and Number Theory 9 (2020), 407--419,
[DOI 10.2140/moscow.2020.9.407](https://doi.org/10.2140/moscow.2020.9.407).
It gives rational separation, not cancellation among the lacunary phases in
(3).

## 4. Typical-point rigidity versus the fixed point \(\pi\)

Primary source: M. Hochman and P. Shmerkin,
[*Equidistribution from Fractal Measures*](https://arxiv.org/abs/1302.5792),
Inventiones Mathematicae 202 (2015), 427--479,
[DOI 10.1007/s00222-014-0573-5](https://doi.org/10.1007/s00222-014-0573-5).

Exact locator: Theorem 1.10. If \(\beta,\gamma>1\), \(\beta\) is Pisot, and
\(\beta,\gamma\) are multiplicatively independent, then every ergodic
\(T_\gamma\)-invariant positive-entropy probability measure is pointwise
\(\beta\)-normal; the conclusion also persists under \(C^2\) diffeomorphisms.
Here “pointwise” means at measure-almost every point.

Substitution: set \(\beta=3\), \(\gamma=10\). The decimal subshift forbidding
\(w\) supports an ergodic positive-entropy Markov/Parry measure \(\mu_w\).
The theorem gives

\[
 \mu_w\text{-almost every }x\in K_w
 \quad\text{is normal in base }3.                              \tag{7}
\]

This is the closest clean positive substitution in the audit. It does not apply
to the actual point \(\pi\): assuming \(w\) is missing only puts the appropriate
decimal tail in \(K_w\); it does not show that this point is generic for
\(\mu_w\), and the theorem gives no effective exceptional-set test. It also
follows the multiplicative sequence \(3^tx\), whereas (3) samples an additive
torsion coset and sums many digital frequencies.

The a.e./fixed-point distinction is mathematically unavoidable, not cosmetic.
For any word \(w\), choose a digit \(d\) appearing in \(w\), and let
\(K^{(d)}\) be the decimal Cantor set whose expansions omit \(d\). Then
\(K^{(d)}\subset K_w\). The natural self-similar measure is power-law (and in
one dimension therefore absolutely decaying). Corollary 1.2 of R. Broderick,
Y. Bugeaud, L. Fishman, D. Kleinbock, B. Weiss,
[*Schmidt's game, fractals, and numbers normal to no base*](https://arxiv.org/abs/0909.4251),
Mathematical Research Letters 17 (2010), 307--321, gives a positive-dimensional
set of \(x\in K^{(d)}\) that are badly approximable and have a bounded number of
consecutive identical digits in every integer base. Such points have
irrationality exponent exactly \(2\), yet their base-3 orbit is not even dense.

Consequently, no theorem whose only hypotheses are

\[
             x\in K_w\quad\text{and}\quad\mu(x)<\infty          \tag{8}
\]

can yield the base-3 distribution needed for ASR. A successful argument must
use further \(\pi\)- or Machin-specific structure.

For an additional boundary on measure-only reasoning, see C. Badea and
S. Grivaux,
[*Around Furstenberg's times \(p\), times \(q\) conjecture: times
\(p\)-invariant measures with some large Fourier coefficients*](https://arxiv.org/abs/2303.01089),
Discrete Analysis 2024:10,
[DOI 10.19086/da.124611](https://doi.org/10.19086/da.124611).
Theorem 1.5 says that, for distinct \(p,q\), a residual set of continuous
\(T_p\)-invariant measures has
\(\limsup_n|\widehat\mu(q^n)|>0\). Corollary 1.6 says that for multiplicatively
independent \(p,q\), generically the full sequence fails to converge to Lebesgue
although convergence holds along a subsequence of upper density one. With
\((p,q)=(10,3)\), invariance and multiplicative independence alone therefore do
not force uniform 3-power Fourier decay. This does not contradict
Hochman--Shmerkin, whose positive-entropy hypothesis is substantive, and it is
not a statement about the particular Parry measure \(\mu_w\).

## 5. Invariant-set intersection theorems

Primary source: M. Wu,
[*A proof of Furstenberg's conjecture on the intersections of
\(\times p\)- and \(\times q\)-invariant sets*](https://arxiv.org/abs/1609.08053),
Annals of Mathematics 189 (2019), 707--751,
[DOI 10.4007/annals.2019.189.3.2](https://doi.org/10.4007/annals.2019.189.3.2).

Exact locator: Theorem 1.4. For closed \(\times p\)-invariant \(A\), closed
\(\times q\)-invariant \(B\), and \(\log p/\log q\notin\mathbb Q\),

\[
 \dim_H((uA+v)\cap B)
 \le\max\{0,\dim_HA+\dim_HB-1\}.                             \tag{9}
\]

Substitution: take \(A=K_w\), \(p=10\), and
\(B=3^{-A}\mathbb Z/\mathbb Z\), \(q=3\). The set \(B\) is finite and
forward \(\times3\)-invariant, so \(\dim_HB=0\). The conclusion is only

\[
                         \dim_H((K_w+v)\cap B)\le0,
\]

which is automatic for an intersection with a finite set and does not imply
emptiness. If one replaces the finite grids by their closure over all exponents,
that closure is the whole circle and (9) becomes tautological in the other
direction. Moreover ASR concerns the finite shadow \(U_{w,n_j}\), not exact
membership in the infinite set \(K_w\).

There is an elementary obstruction to hoping that a dimension theorem secretly
gives eventual emptiness. For any nonempty word \(w\) of length \(m\), choose
\(d\in\{1,\ldots,8\}\) with \(w\ne d^m\). Then

\[
                    x=\frac d9=0.\overline d\in K_w,
\]

and \(x\in3^{-A}\mathbb Z/\mathbb Z\) for every \(A\ge2\). Thus unshifted
nested triadic grids meet \(K_w\) forever. Any viable theorem must exploit the
actual varying translate \(\alpha_j\), and a statement uniform in all translates
is false for the trivial reason that a translate may be chosen through a survivor.

## 6. Restricted-digit Fourier estimates

Primary source: J. Maynard,
[*Primes with restricted digits*](https://arxiv.org/abs/1604.01041),
Inventiones Mathematicae 217 (2019), 127--218,
[DOI 10.1007/s00222-019-00865-6](https://doi.org/10.1007/s00222-019-00865-6).

Exact locator: Lemma 8.2, restated as Lemma 10.1. For the normalized Fourier
product \(F_Y\) of the one-missing-digit set, if

\[
 q<Y^{1/3},\qquad q=q_1q_2,qquad(q_1,10)=1,qquad q_1>1,
 \qquad |\eta|<Y^{-2/3}/2,
\]

then for \((a,q)=1\),

\[
 F_Y(a/q+\eta)\ll
 \exp\!\left(-c\frac{\log Y}{\log q}\right).                \tag{10}
\]

Positive substitution: at an ordinary rational frequency \(a/3^A\), take
\(q_1=3^A,q_2=1,\eta=0\). When the size condition holds, (10) gives strong
decay of the one-missing-digit Fourier coefficient.

Exact ASR substitution: its digital coefficient is

\[
 S_{w,n}(\ell D_j)
 =\sum_{k\in A_w(n)}e\!\left(-\frac{\ell D_jk}{10^n}\right).
\]

After reduction, the rational frequency \(\ell D_j/10^n\) has denominator
dividing \(10^n\), hence containing only the primes \(2\) and \(5\). In any
factorization required by (10), the component coprime to \(10\) is therefore
\(q_1=1\), contradicting the hypothesis \(q_1>1\). ASR lies exactly on the
base-10 major aliases excluded by Lemma 8.2. In addition, Maynard treats one
missing digit, not an arbitrary forbidden finite word, and his later prime
argument obtains cancellation after coupling and averaging arithmetic sums;
it gives no pointwise value of (3).

This rejection is stronger than a mere modulus-range mismatch: the relevant
frequency fails the structural coprimality hypothesis at every depth.

## 7. Fixed-modulus digit distribution

Primary source: V. Saavedra-Araya,
[*Distribution of integers with digit restrictions via Markov
chains*](https://doi.org/10.1017/etds.2025.10256), Ergodic Theory and
Dynamical Systems 46 (2026), 757--804.

Exact locators:

* **Theorem 4.9.** For a vector of \(g\)-additive functions eventually
  periodic modulo a fixed vector \(\mathbf a\), and a mixing, sofic, regular
  subshift satisfying the Markov condition, the restricted integers become
  uniformly distributed among the fixed residue classes.
* **Theorem 5.11.** This verifies a special joint residue/digit-sum conclusion
  for an irreducible regular one-step SFT under explicit digit and coprimality
  hypotheses.
* **Theorem C / Theorem 6.7.** For a transitive sofic model, the mass dimension
  of the intersection with an infinite arithmetic progression is either zero
  or the full mass dimension.

For \(g=10\), \(f(n)=n\), and a **fixed** modulus \(3^A\), Theorem 4.9 is a
possible route only when the relevant mixing, sofic, regular-presentation and
Markov hypotheses are separately verified; this audit does not assert them for
every one-word avoidance shift. Even when it applies, the theorem is not uniform
in \(A\), whereas T52 requires \(A=a_j-1\to\infty\) jointly with
\(n_j\asymp j\).

More importantly, even a uniform growing-modulus version would address the
wrong sample. Residue distribution counts

\[
                        k\in A_w(n),\quad k\equiv b\pmod{3^A}.
\]

ASR instead tests the \(D\) Beatty positions

\[
       k_c=\left\lfloor10^n\left(\frac cD+\alpha\right)\right\rfloor,
       \qquad 0\le c<D,                                      \tag{11}
\]

spread across the whole interval. Fourier duality makes the distinction exact:
residue classes use frequencies of denominator \(D\), while (11) produces the
frequencies \(\ell D/10^n\) in (3). Theorem C likewise gives a dimension
dichotomy, not emptiness or a signed actual-phase bound.

## 8. Rational points in missing-digit Cantor sets

Primary source: S. Chow, P. Varju, H. Yu,
[*Counting rationals and Diophantine approximation in missing-digit Cantor
sets*](https://arxiv.org/abs/2402.18395), Advances in Mathematics 488 (2026),
110807,
[DOI 10.1016/j.aim.2026.110807](https://doi.org/10.1016/j.aim.2026.110807).

Exact locators:

* **Theorem 1.2.** If \(b\ge5\) and exactly one base-\(b\) digit is missing
  (plus the two stated \(b=4\) cases), then for
  \(\kappa=\dim_HK\) there is an effective \(\varrho>0\) such that
  \[
                 \mathcal N_K(T)\ll T^{2\kappa-\varrho}.
  \]
* **Theorem 2.1.** The same type of saving follows for a
  \(\kappa\)-regular measure whose Fourier \(\ell^1\) dimension exceeds
  \(1/2\).

These are aggregate upper bounds for all rational points of height at most
\(T\) lying in an **infinite** Cantor set. They do not say the count is zero,
do not isolate a prescribed denominator or numerator phase, and Theorem 1.2
does not cover an arbitrary forbidden word.

There is also a decisive finite/infinite mismatch. Under a missing-word shadow,
the rational Machin point is known only to lie in the depth-\(n_j\) union
\(U_{w,n_j}\). Its later rational digits may contain \(w\), so it need not lie
in \(K_w\) at all. Rational counting in \(K_w\) therefore cannot be applied to
the witness counted by \(N_j\).

## 9. Sharp missing premise

After all substitutions, the unfilled slot is still exactly this: for every
nonempty finite word \(w\), control the actual Machin phases

\[
 \theta_j=\frac{r_j}{F_j}=\{D_jx_j\},qquad
 D_j=3^{a_j-1},qquad n_j=2j+|w|-1,
\]

in the signed sum

\[
 \lim_{H\to\infty}\sum_{0<|\ell|\le H}
 \frac{1-e(-\ell D_j/10^{n_j})}{2\pi i\ell}
 S_{w,n_j}(\ell D_j)e(\ell\theta_j).                         \tag{12}
\]

A theorem proving (6) at one valid missing-word shadow scale would suffice; the
clean uniform version is the second half of ASR in (5). Any such theorem must
simultaneously have all of the following features:

* **Pointwise:** it applies to the actual fixed \(\pi\)/Machin phase, not
  \(\mu\)-almost every phase or an averaged shift.
* **Moving and linked:** \(D_j\asymp j\), its exponent is
  \(a_j-1\asymp\log_3j\), and the digit depth is \(n_j\asymp2j\).
* **Alias-sensitive:** it handles the rational frequencies
  \(\ell D_j/10^{n_j}\), whose reduced denominators are base-10 powers and
  therefore sit on the excluded major aliases of (10).
* **Signed:** it exploits cancellation in the whole reconstruction (12), not
  merely \(\sum|S_{w,n}(h)|\).
* **Cross-index or phase-specific:** it uses information beyond the denominator
  valuation, since (4) shows that the CRT-localized character recombines to the
  original Archimedean phase.

The Broderick--Bugeaud--Fishman--Kleinbock--Weiss construction proves that
membership in \(K_w\) plus even optimal irrationality exponent is insufficient.
The triadic rational \(d/9\) proves that an unshifted-grid exclusion is false.
The exact experiment already recorded in
[`actual_shift_resonance_attack.md`](actual_shift_resonance_attack.md) gives
\(j=35,D_j=81\) and a one-digit forbidden word with

\[
 N_j=1,\qquad Z_j=0.050752878605\ldots,\qquad
 \mathcal R_j=0.949247121394\ldots,
\]

so the tempting uniform relative bound \(|\mathcal R_j|\le Z_j\) is false even
for the exact actual shift. This remains an `experiment`, not an asymptotic
claim.

## 10. Bottom line

The 3-primary denominator is genuine and persistent, but it is not yet a
distribution theorem. Furstenberg and BLMV rigorously place \(\pi\) in a dense,
partly effective two-parameter \((10,3)\) orbit; Hochman--Shmerkin rigorously
make typical points of the missing-word fractal base-3 normal; Maynard and
Saavedra-Araya rigorously control nearby Fourier/residue problems; Wu and
Chow--Varju--Yu rigorously constrain invariant-set intersections and rational
counts. Every substitution stops before the same point: none controls (12) at
the actual moving seed.

Accordingly, there is no complete proof to import from these sources. The next
meaningful mathematical advance must prove a pointwise actual-phase estimate
such as (6), or discover additional cross-index structure of
\(\theta_j=\{D_jx_j\}\) strong enough to imply it. Repackaging the nested
3-primary denominator as a multiplicative orbit, a residue class, or a Cantor
intersection does not close the gap.

## Primary-source index

1. Furstenberg 1967, Theorem IV.1:
   [primary PDF](https://www.math.ucsd.edu/~asalehig/F_Disjointness.pdf);
   [DOI](https://doi.org/10.1007/BF01692494).
2. Bourgain--Lindenstrauss--Michel--Venkatesh 2009, Theorems 1.4, 1.8,
   1.10 and Corollary 1.6:
   [primary PDF](https://math.stanford.edu/~akshay/research/blmv.pdf);
   [DOI](https://doi.org/10.1017/S0143385708000898).
3. Zeilberger--Zudilin 2020, finite irrationality measure for \(\pi\):
   [arXiv](https://arxiv.org/abs/1912.06345);
   [DOI](https://doi.org/10.2140/moscow.2020.9.407).
4. Hochman--Shmerkin 2015, Theorem 1.10:
   [arXiv](https://arxiv.org/abs/1302.5792);
   [DOI](https://doi.org/10.1007/s00222-014-0573-5).
5. Broderick--Bugeaud--Fishman--Kleinbock--Weiss 2010, Corollary 1.2:
   [arXiv](https://arxiv.org/abs/0909.4251).
6. Wu 2019, Theorem 1.4:
   [arXiv](https://arxiv.org/abs/1609.08053);
   [DOI](https://doi.org/10.4007/annals.2019.189.3.2).
7. Maynard 2019, Lemma 8.2 / Lemma 10.1:
   [arXiv](https://arxiv.org/abs/1604.01041);
   [DOI](https://doi.org/10.1007/s00222-019-00865-6).
8. Saavedra-Araya 2026, Theorems 4.9, 5.11, C / 6.7:
   [primary journal article](https://doi.org/10.1017/etds.2025.10256).
9. Chow--Varju--Yu 2026, Theorems 1.2 and 2.1:
   [arXiv](https://arxiv.org/abs/2402.18395);
   [DOI](https://doi.org/10.1016/j.aim.2026.110807).
10. Badea--Grivaux 2024, Theorem 1.5 and Corollary 1.6:
    [arXiv](https://arxiv.org/abs/2303.01089);
    [DOI](https://doi.org/10.19086/da.124611).
