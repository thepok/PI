# Actual shifted-grid resonance for the Machin seed

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local source contains no external source URL,
so none is invented here.  
Route: the exact missing estimate in
[`subexponential_candidate_avoidance.md`](subexponential_candidate_avoidance.md),
the numerator split in
[`actual_numerator_phase_attack.md`](actual_numerator_phase_attack.md), and
the growing high-prime bands in
[`general_seed_band_attack.md`](general_seed_band_attack.md).

## Outcome and exact status

No proof that every finite decimal word occurs in \(\pi\) was obtained. The
canonical target remains a `conjecture`.

The useful result is an exact identification of the missing Fourier
estimate. Sampling the word-avoidance set on the shifted \(D_j\)-grid kills
every Fourier frequency except a multiple of \(D_j\). At the surviving
frequency \(\ell D_j\), the actual Machin remainder contributes exactly

\[
                         e\!\left({\ell r_j\over F_j}\right).
\]

The localized prime formulas make this phase an explicit product of local
additive characters. They do **not** average those characters: the product
recombines to the single linear character above. More decisively,

\[
 {r_j\over F_j}=\{D_jx_j\},\qquad
 x_j=\{10^jM_{3j}\},                              \tag{1}
\]

so the allegedly new resonant phase is exactly the actual Archimedean
Machin phase after multiplication by \(D_j\). A cancellation estimate for it
at the required scale is therefore fixed-\(\pi\) numerator distribution, not
a consequence of the local denominator calculation.

Equations (7), (10), and (16) below are elementary exact identities, recorded
as a `proof sketch` because they have not been added to the verified Lean
track. The primary-source applicability audit in Section 7 is
`literature-checked` as of the displayed date. No separator is claimed here:
one that preserved the actual \(D_j,F_j,r_j\) and the same avoidance set
would preserve the count itself and would amount to settling the missing
estimate rather than separating it.

## 1. Normalized target and quantifiers

The canonical V1 statement is

\[
 \forall m\in\mathbb N\;\forall w\in\{0,\ldots,9\}^{m}\;
 \exists n\in\mathbb N:\quad
 (d_n(\pi),\ldots,d_{n+m-1}(\pi))=w.              \tag{2}
\]

Digits are after the decimal point, leading zeroes in \(w\) are allowed,
and \(m=0\) is vacuous. The target is contiguous finite occurrence, not
subsequence occurrence and not normality.

Fix below a nonempty word \(w\) of length \(m\). Avoidance at the \(T\)
starting positions \(0,\ldots,T-1\) is the same as avoidance in a string of
length

\[
                         n=T+m-1,\qquad M=10^n.    \tag{3}
\]

Let \(A_w(n)\subset\{0,\ldots,M-1\}\) be the integers whose length-\(n\),
leading-zero-padded decimal string avoids \(w\), and write
\(a_w(n)=|A_w(n)|\). With the half-open convention, the survivor set is

\[
 U_{w,T}=\bigcup_{k\in A_w(n)}
       \left[{k\over M},{k+1\over M}\right).      \tag{4}
\]

## 2. The shifted grid and an exact boundary-safe finite formula

At one reduced rational Machin seed, write

\[
 x={b\over Q},\qquad Q=FD,\quad(F,D)=1,\quad
 b=Fc+r,\quad 0\le r<F.                           \tag{5}
\]

The local calculations determine \(r=b\bmod F\), while the coarse quotient
ranges over \(0\le c<D\). Put

\[
 \alpha={r\over FD},\qquad
 N(D,r;w,T)=\sum_{c=0}^{D-1}
    \mathbf1_{U_{w,T}}\!\left({c\over D}+\alpha\right).        \tag{6}
\]

There is a finite Fourier identity which is valid without any endpoint
qualification. Define on \(\mathbb Z/Q\mathbb Z\)

\[
 g(a)=\mathbf1_{A_w(n)}\!\left(\left\lfloor{Ma\over Q}\right\rfloor\right),
 \qquad
 G(h)=\sum_{a=0}^{Q-1}g(a)e\!\left(-{ha\over Q}\right).
\]

The numerator alternatives are the coset \(Fc+r\), so finite Fourier
inversion and subgroup orthogonality give exactly

\[
 \boxed{
 N(D,r;w,T)={1\over F}\sum_{u=0}^{F-1}
       G(Du)e\!\left({ur\over F}\right).}         \tag{7}
\]

Thus the resonant frequencies are already forced to be multiples of \(D\),
and the actual remainder already occurs only through the additive character
of \(r\bmod F\). Formula (7) is finite but its transform \(G\) hides the
decimal automaton. The Poisson form below exposes that automaton and its
zero-mode main term.

## 3. Exact Poisson formula on the circle

Use \(e(z)=\exp(2\pi iz)\) and
\(\widehat f(h)=\int_0^1f(x)e(-hx)\,dx\). For
\(f=\mathbf1_{U_{w,T}}\), define the digital Fourier sum

\[
 S_{w,n}(h)=\sum_{k\in A_w(n)}e\!\left(-{hk\over M}\right).   \tag{8}
\]

Direct integration over the cylinders in (4) gives

\[
 \widehat f(0)={a_w(n)\over M},\qquad
 \widehat f(h)={1-e(-h/M)\over2\pi i h}\,S_{w,n}(h)
 \quad(h\ne0).                                     \tag{9}
\]

Summing the Fourier series over \(\alpha+c/D\) annihilates all frequencies
not divisible by \(D\). Whenever no sampled point is a cylinder endpoint,
Dirichlet convergence therefore gives the exact symmetric-limit identity

\[
 \boxed{
 \begin{aligned}
 N(D,r;w,T)
  ={}&{D\,a_w(n)\over M}\\
   &+\lim_{H\to\infty}\sum_{0<|\ell|\le H}
     {1-e(-\ell D/M)\over2\pi i\ell}\,
     S_{w,n}(\ell D)e\!\left({\ell r\over F}\right).
 \end{aligned}}                                    \tag{10}
\]

The endpoint condition is automatic for all sufficiently large seeds in the
intended split. Indeed, reducedness gives \((r,F)=1\). If a sample equalled
\(k/M\), then reducing
\(M(Fc+r)=kFD\) modulo \(F\) would give \(F\mid M\). The growing high-prime
factor of \(F\) contains a prime other than \(2,5\), so this is impossible.
For any finite exceptional seed, (7) remains exact with the half-open floor
convention.

### The forbidden-word transfer matrix

Formula (10) can be made completely finite-state. Let the states be the
proper prefixes of \(w\), with a state recording the longest current suffix
which is a prefix of \(w\). For each digit \(a\), let \(A_a\) be the
zero-one transition matrix for appending \(a\), with the transition deleted
when it completes \(w\). If \(v_0\) is the empty-prefix state and
\(\mathbf1\) is the all-ones terminal vector, then

\[
 \boxed{
 S_{w,n}(h)=v_0^{\mathsf T}
   \prod_{t=1}^{n}\left(
      \sum_{a=0}^{9}e\!\left(-{ha\over10^t}\right)A_a
   \right)\mathbf1.}                              \tag{11}
\]

The order in (11) is from the most significant to the least significant
digit. This is the exact matrix product whose spectral radius at \(h=0\)
gives the ordinary avoidance entropy. At \(h=\ell D\), it is the digital
coefficient in the unresolved resonant sum (10).

## 4. What the high-prime formulas do to the phase

Return to the exact seed

\[
 y_j=10^jM_{3j}={a_j\over Q_j},\qquad
 x_j=\{y_j\}={b_j\over Q_j},\qquad Q_j=F_jD_j.     \tag{12}
\]

The reduced numerators satisfy \(b_j\equiv a_j\pmod{Q_j}\). Let
\(P_j\mid F_j\) be the squarefree product of the certified high primes, and
write \(F_j=F_{0,j}P_j\), where \(F_{0,j}\) contains the other complete
primary components. For a component \(q\in\{F_{0,j}\}\cup\{p:p\mid P_j\}\),
put

\[
 u_{j,q}\equiv a_j(Q_j/q)^{-1}\pmod q.            \tag{13}
\]

For a high prime \(p\), this is simply the localized unit
\(u_{j,p}\equiv p y_j\pmod p\). Additive CRT gives

\[
 e\!\left({\ell r_j\over F_j}\right)
 =e_{F_{0,j}}(\ell D_j u_{j,F_{0,j}})
   \prod_{p\mid P_j}e_p(\ell D_j u_{j,p}),         \tag{14}
\]

where \(e_q(z)=e(z/q)\). The cancellation of the CRT inverses in (14) is
exact: modulo \(q\),

\[
 r_j(F_j/q)^{-1}
 \equiv (Q_j/q)u_{j,q}(F_j/q)^{-1}
 \equiv D_j u_{j,q}.                              \tag{15}
\]

If \(p\) lies in the band
\(d/(2s+1)<p\le d/(2s-1)\), with \(d=12j+3\), and is not an endpoint or a
coefficient exception, the general-band calculation supplies

\[
 u_{j,p}\equiv10^j\chi_4(p)C_s\pmod p.
\]

Consequently the known high-prime part of the actual resonant phase is

\[
 \boxed{
 \prod_{p\mid P_j}
 e_p\!\left(\ell D_j10^j\chi_4(p)C_{s(p)}\right).} \tag{16}
\]

Here the rational \(C_{s(p)}\) is interpreted in \(\mathbb F_p\); the stated
exceptions ensure that its denominator is invertible modulo \(p\).

This is more explicit than merely saying that \(r_j\) is known by CRT, but it
does not itself create cancellation. The primes in (16) are fixed
components of one modulus; there is no sum over \(p\). All factors have
modulus one, share the same frequency \(\ell\), and their product is exactly
the single linear character in (14).

The only automatic orthogonality is over a complete \(F_j\)-period:

\[
 \sum_{\ell=0}^{F_j-1}e(\ell r_j/F_j)=0,
\]

because \((r_j,F_j)=1\). It does not apply to (10), whose digital coefficient
varies with \(\ell\). It is also on the wrong scale. Along the existing
\(T\le2j+O_w(1)\) pulse, \(M=10^{2j+O_w(1)}\), while the general prime-band
result gives

\[
 \log F_j\ge12j-o(j),\qquad
 \log M\le2j\log10+O_w(1).
\]

Hence the natural low-frequency block \(|\ell|\lesssim M/D_j\) is
exponentially shorter than one period of the high-prime character. Merely
knowing that the character is primitive gives a separation of order
\(1/F_j\), far smaller than the \(1/M\)-scale needed to rule out its digital
major arcs.

## 5. Euclidean reciprocity makes the phase circular

Equation (1) follows directly from the quotient split:

\[
 D_jx_j={b_j\over F_j}=c_j+{r_j\over F_j}.
\]

Therefore, for every integer \(\ell\),

\[
 \boxed{
 e\!\left({\ell r_j\over F_j}\right)
       =e(\ell D_jx_j).}                          \tag{17}
\]

Thus (16) is an exact local factorization of the already-selected actual
Archimedean phase. T38 identifies \(x_j\) with a summably perturbed decimal
\(\pi\)-orbit point. Replacing (17) by its CRT product changes coordinates,
not information.

There is a useful logical check. Under a missing-word hypothesis, after a
valid T38/T46 shadow transfer the actual point \(x_j\) lies in
\(U_{w,T}\). Its actual quotient \(c_j\) is one of the points counted in
(6), so

\[
                         N(D_j,r_j;w,T)\ge1.       \tag{18}
\]

On the other hand, the avoidance entropy and \(D_j=\exp(o(j))\) give, for
\(T=\Theta(j)\),

\[
                    {D_j a_w(n)\over10^n}=o(1).   \tag{19}
\]

Combining (10), (18), and (19) shows that the missing-word hypothesis forces
the nonzero resonant contribution to be at least \(1-o(1)\). A proof must
rule out exactly that phase-aligned contribution; no zero-mode estimate can
do it.

## 6. The first exact unsolved exponential sum

Substituting (11) and (14) into (10) isolates the first missing estimate.
With

\[
 B_t(h)=\sum_{a=0}^{9}e(-ha/10^t)A_a,
\]

define

\[
\begin{aligned}
 \mathcal R_{j,w,n}:={}&
 \lim_{H\to\infty}\sum_{0<|\ell|\le H}
 {1-e(-\ell D_j/10^n)\over2\pi i\ell}\,
 v_0^{\mathsf T}\!\left(\prod_{t=1}^{n}B_t(\ell D_j)\right)\!\mathbf1\\
 &\qquad\qquad\cdot
 e_{F_{0,j}}(\ell D_ju_{j,F_{0,j}})
 \prod_{p\mid P_j}
 e_p\!\left(\ell D_j10^j\chi_4(p)C_{s(p)}\right).
                                                               \tag{20}
\end{aligned}
\]

Every symbol in (20) is fixed by the finite word automaton and the exact
rational Machin seed. The exact identity is

\[
 N(D_j,r_j;w,T)={D_ja_w(n)\over10^n}+\mathcal R_{j,w,n}.        \tag{21}
\]

A sufficient new theorem would give

\[
 \mathcal R_{j,w,n}<1-{D_ja_w(n)\over10^n}                     \tag{22}
\]

for at least one valid shadow scale under the assumption that \(w\) is
missing. An absolute bound tending to zero would be stronger than needed.
No such estimate is proved here. Equation (17) explains why it is hard:
(20) is a digit-automaton Fourier reconstruction evaluated at the one actual
Machin/\(\pi\) phase.

Absolute-value Fourier bounds are structurally too weak. If a normalized
avoidance measure has Fourier \(\ell^1\) dimension \(s\), summing absolute
values up to scale \(M\) costs about \(M^{1-s}\). Since the avoidance set
has size about \(M^\kappa\) and necessarily \(s\le\kappa\), this loses the
entire entropy saving at the endpoint even before the factor \(D_j\). The
needed information is signed cancellation with the actual phase in (20),
not another bound for \(\sum|S_{w,n}(h)|\).

## 7. Dated primary-source applicability audit (`literature-checked`)

Search cutoff: **2026-08-12 UTC**. The following are the closest primary
results located; none supplies (22).

1. Maynard's *Primes with restricted digits* develops explicit Fourier
   products, \(\ell^1\)/moment estimates, and hybrid rational-frequency
   bounds for a one-missing-digit language. Its cancellation comes after
   coupling the digital transform to prime Type I/II sums and averaging the
   relevant arithmetic structure. It gives no pointwise bound for the one
   character \(e(\ell r_j/F_j)\) in (20):
   [arXiv:1604.01041](https://arxiv.org/abs/1604.01041).
2. Erdős--Mauduit--Sárközy prove quantitative equidistribution of
   missing-digit integers in residue classes for moduli up to
   \(\exp(c\sqrt{\log N})\), under coprimality hypotheses. The theorem is
   distribution among residue classes, not exclusion from one translated
   Beatty/grid sample; its modulus range also does not cover a general
   \(D_j=\exp(o(j))\):
   [DOI 10.1006/jnth.1998.2229](https://doi.org/10.1006/jnth.1998.2229).
3. Saavedra-Araya's 2026 Markov-chain theorem treats fixed-modulus limiting
   distribution for missing digits and some finite-type/sofic digit
   restrictions, including forbidden combinations. Its hypotheses and
   convergence are for a fixed modulus coprime to the base; (20) uses a
   growing modulus and a short interval in the base-power cyclic group at
   the same scale as the digits:
   [arXiv:2411.07418v2](https://arxiv.org/abs/2411.07418v2),
   [journal DOI](https://doi.org/10.1017/etds.2025.10256).
4. Chow--Varj\'u--Yu bound the number of bounded-height rationals in
   one-missing-digit Cantor sets using Fourier \(\ell^1\) dimension. Their
   result is a polynomial rational-counting theorem, not a zero-count theorem
   for a prescribed shifted denominator grid at depth
   \(10^{-\Theta(j)}\); it also supplies no special information about the
   Machin shift:
   [arXiv:2402.18395v2](https://arxiv.org/abs/2402.18395v2),
   [published DOI](https://doi.org/10.1016/j.aim.2026.110807).

The search found strong average, family, fixed-modulus, and rational-counting
theorems, but no primary theorem controlling the deterministic product in
(20) for a single changing Machin phase. This is a bounded dated search, not
a claim that the literature is exhausted.

## 8. Sharp continuation lemma and no false separator

The next useful lemma must exploit the special CRT reconstruction in (16) in
an Archimedean way. Alternative sufficient continuation routes include:

- a signed bound for (20) below the integer threshold in (22);
- a quantitative exclusion of \(r_j/F_j\) from the digital major arcs of the
  transfer products \(S_{w,n}(\ell D_j)\); or
- a cross-index theorem showing that the exact CRT phases (17), not merely
  alternative quotient states, cannot remain in the avoidance automaton.

Nonzeroness of every local residue, primitivity of the global character,
complete-period orthogonality, Fourier \(\ell^1\) dimension, or
fixed-modulus digit equidistribution does not give any of these statements.

No new separator is manufactured in this note. The existing artificial
shift separators correctly show that denominator size and fine-carry data
alone are insufficient, but they do not preserve the full actual phase
\(r_j/F_j\). Conversely, once \((D_j,F_j,r_j)\) and \(U_{w,T}\) are all
preserved, (6) fixes \(N\) exactly; constructing an avoiding member is the
same occupancy question as (22).

## 9. Concrete transfer diagonalization and cross-scale audit

The most direct spectral attempt does not contract the dangerous digital
aliases. Put

\[
                         A=\sum_{a=0}^{9}A_a.
\]

For integers \(h\) and \(0\le v<n\), the matrices in (11) satisfy exactly

\[
 B_t(10^vh)=
 \begin{cases}
 A,&t\le v,\\
 B_{t-v}(h),&t>v.
 \end{cases}
\]

Consequently

\[
 \boxed{
 S_{w,n}(10^vh)=v_0^{\mathsf T}A^v
       \left(\prod_{s=1}^{n-v}B_s(h)\right)\mathbf1.}          \tag{23}
\]

The usual forbidden-word automaton over ten digits is primitive. Perron--
Frobenius/Jordan decomposition therefore gives

\[
 A^v=\lambda_w^vP_w+
 O_w\!\left(v^{m-1}\lambda_{*,w}^v\right),
 \qquad \lambda_{*,w}<\lambda_w<10.             \tag{24}
\]

Thus diagonalization leaves a leading term of size \(\lambda_w^v\) on the
power-of-ten aliases; it does not give a uniform spectral gap there. For a
one-digit forbidden word the matrices are scalar and the obstruction is
even exact:

\[
                         S_{w,n}(10^vh)=9^vS_{w,n-v}(h).        \tag{25}
\]

In (20), take \(\ell=10^vq\). The phase paired with (23) is

\[
 e(10^vq r_j/F_j)=e(q10^vD_jx_j).
\]

Let \(s_j=10^j(\pi-M_{3j})\), as in T38. Since
\(x_j\equiv10^j\pi-s_j\pmod1\), this is exactly

\[
 e(q10^vD_jx_j)
 =e(qD_j10^{j+v}\pi)e(-qD_j10^vs_j).              \tag{26}
\]

For \(|q|D_j10^v\le10^n\), T38's \(0\le s_j<\rho^j\) gives the explicit
comparison

\[
 \left|e(q10^vD_jx_j)-e(qD_j10^{j+v}\pi)\right|
 \le2\pi10^n\rho^j.                              \tag{27}
\]

At \(n\le2j+m-1\), the right side is at most
\(2\pi10^{m-1}(100\rho)^j\), with
\(100\rho\simeq4.096\cdot10^{-6}\). The Machin shadow therefore removes
the tiny forcing error, but it leaves the lacunary fixed-\(\pi\) phases
\(e(qD_j10^{j+v}\pi)\). The available finite irrationality-measure bound for
\(\pi\) gives individual rational-separation estimates; it does not supply a
bound for these signed, variable-frequency lacunary sums.

The recurrence across seed indices also fails to close this frequency
family. T38 gives

\[
 e(\ell D_{j+1}x_{j+1})
 =e(10\ell D_{j+1}x_j)e(\ell D_{j+1}\Delta_j).    \tag{28}
\]

To identify the first factor with a frequency on the \(j\)-th
\(D_j\)-resonant lattice would require
\(D_j\mid10\ell D_{j+1}\). The reduced complementary denominators are not
nested, and no such divisibility holds uniformly. Allowing a different
frequency at every step merely changes (28) into the variable-frequency
fixed-\(\pi\) sum in (26). Thus neither Perron diagonalization nor the exact
Machin coboundary yields (22).

### A theorem-sized remaining hypothesis

The arithmetic content can now be stated with an exact integer margin. For
a nonempty word \(w\) of length \(m\), set \(n_j=2j+m-1\) and use the
intended high-prime split \(Q_j=F_jD_j\). The following statement would be
sufficient:

> **Actual-shift resonance hypothesis \(\mathrm{ASR}(w)\).** There is
> \(J_w\) such that for every \(j\ge J_w\),
> \[
> {D_ja_w(n_j)\over10^{n_j}}\le{1\over4},\qquad
> |\mathcal R_{j,w,n_j}|\le{1\over2}.             \tag{29}
> \]

The first inequality follows eventually from the already established
\(D_j=\exp(o(j))\) and avoidance entropy. The second is the new signed
arithmetic cancellation assertion. Equations (21) and (29) would give
\(0\le N\le3/4\), hence \(N=0\). At any scale where the missing-word shadow
transfer gives (18), this is a contradiction. A stronger, more conventional
pointwise discrepancy theorem of the form

\[
 |\mathcal R_{j,w,n_j}|\le C_wD_j10^{-\eta_wj}
 \quad(j\ge J_w),\qquad \eta_w>0,                 \tag{30}
\]

would imply the second half of (29). Neither (29) nor (30) is proved here;
they are `conjecture` statements, not conditional resolutions.

### Exact falsification experiment

[`actual_shift_resonance_check.py`](actual_shift_resonance_check.py),
SHA-256
`9933571acab5536921b646e02398d541877d5778817835fceaca92c4bf111ed4`,
tests the most tempting stronger bound before it can be mistaken for (29).
It uses the exact finite Machin seed and freezes **every** denominator
component except the complete 3-primary component. Thus

\[
 D_j=3^{v_3(Q_j)},\qquad F_j=Q_j/D_j,
\]

so the split preserves the actual base and high-prime residues (and more),
while leaving a genuine coprime shifted grid. For one-digit avoidance at
length \(2j\), it computes each prefix by the exact integer identity

\[
 \left\lfloor10^{2j}\left({c\over D_j}
       +{r_j\over F_jD_j}\right)\right\rfloor
 =\left\lfloor{10^{2j}c+\lfloor10^{2j}r_j/F_j\rfloor
                    \over D_j}\right\rfloor.      \tag{31}
\]

Commands:

```bash
python3 -m py_compile \
  work/ultrapi-resume/actual_shift_resonance_check.py
python3 work/ultrapi-resume/actual_shift_resonance_check.py --max-j 80
```

The retained run reports 8,580 exact prefix checks. Its strongest row is
\(j=35\), \(D_j=81\), for each of the forbidden digits 4 and 5:

\[
 N=1,\qquad D_j(9/10)^{70}=0.050752878605\ldots,
 \qquad\mathcal R=0.949247121394\ldots.            \tag{32}
\]

The occupancy is \(19.7033\ldots\) times its zero-mode expectation. At the
next seed, with the same \(D=81\), both counts are zero and
\(\mathcal R=-0.041109831670\ldots\). The full retained output is:

```text
claim_status=experiment
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
split=complementary modulus is the complete 3-primary denominator
pulse=one-digit avoidance at length 2*j
j_range=1..80
exact_prefix_checks=8580
subunit_zero_mode_survivor_rows=90
naive_bound_abs_resonance_le_zero_mode_violations=65
last_survival_by_digit={'0': 28, '1': 27, '2': 16, '3': 20, '4': 35, '5': 35, '6': 22, '7': 28, '8': 28, '9': 28}
largest_resonance=j:35,digit:4,D:81,N:1,zero_mode:0.050752878606,signed_resonance:0.949247121394,occupancy_over_zero_mode:19.703315899974
largest_resonance_witness_prefix=1728033596905970018505808789838680603817073196158899022872981265513012
next_scale=j:36,digit:4,D:81,N:0,zero_mode:0.041109831671,signed_resonance:-0.041109831671
largest_resonance=j:35,digit:5,D:81,N:1,zero_mode:0.050752878606,signed_resonance:0.949247121394,occupancy_over_zero_mode:19.703315899974
largest_resonance_witness_prefix=2839144708017081129616919900949791714928184307270010133984092376624123
next_scale=j:36,digit:5,D:81,N:0,zero_mode:0.041109831671,signed_resonance:-0.041109831671
all exact checks passed
```

This `experiment` falsifies the naive uniform relative estimate
\(|\mathcal R|\le D_j\mu(U_{w,T})\), even for a split retaining the actual
Machin residues. It does not falsify the eventual intended-split hypothesis
(29), does not prove that any word occurs in \(\pi\), and is not evidence for
an untested asymptotic. Its purpose is to prevent a Perron eigenvalue or
random-shift heuristic from being promoted to a pointwise theorem.

## Bottom line

The shifted-grid Poisson problem is now explicit down to one formula. The
high-prime Machin residues factor the resonant phase into known local
characters, but those characters immediately recombine to
\(e(\ell r_j/F_j)=e(\ell D_jx_j)\). At a missing-word scale the zero mode is
\(o(1)\), while the missing hypothesis forces the signed resonant sum (20)
to contribute at least \(1-o(1)\). No located theorem cancels that one
actual phase, and no unconditional cylinder hit, candidate resolution, or
verified resolution follows.
