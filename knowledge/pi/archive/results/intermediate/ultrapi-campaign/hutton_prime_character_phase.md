# Hutton signed prime-reciprocal phase: sharp bounds, product structure, and the moving-frequency barrier

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question has no external source URL;
none is invented here.  This is a focused continuation of
[`hutton_global_crt_attack.md`](hutton_global_crt_attack.md), following the
fields of [`problems/TEMPLATE.md`](../../problems/TEMPLATE.md) inside the
existing problem record.

## Outcome and claim status

No proof that every finite decimal word occurs in pi was obtained.  The
canonical V1 statement remains a `conjecture`.

For

\[
 R=4K+3,\qquad
 \mathcal P_K=\{p:R/2<p\le R,\ p>7,\ p\ne17\},
\]

put

\[
 \epsilon_p=\chi_4(p)=(-1)^{(p-1)/2},\qquad
 \Delta_K=\sum_{p\in\mathcal P_K}{\epsilon_p\over p}
          ={S_K\over G_K},\qquad
 G_K=\prod_{p\in\mathcal P_K}p.                       \tag{1}
\]

The exact identities and inequalities derived below are `proof sketch`:
their elementary derivations are written out, but they are not Lean
declarations.  The primary-source audit is `literature-checked` as of the date
above.  The finite replay is an `experiment`.  Nothing here is a `candidate
resolution`.

There are four material findings.

1. Abel summation plus the strongest fixed-modulus prime-number-theorem input
   found in the bounded search gives

   \[
   \Delta_K\ll {1\over\log R}
    \exp\!\left(-c{(\log R)^{3/5}\over(\log\log R)^{1/5}}\right)              \tag{2}
   \]

   unconditionally, with effective constants.  Under GRH it gives the
   pointwise bound

   \[
   \Delta_K=O\!\left({\log R\over\sqrt R}\right).                            \tag{3}
   \]

   A fully numerical unconditional bound and a fully numerical GRH bound are
   recorded below.
2. Neither estimate survives the mandatory Hutton transient.  If

   \[
   b_K=\lfloor\log_5R\rfloor,\qquad
   \alpha={\log10\over\log5}=1.430676558\ldots,                              \tag{4}
   \]

   then \(10^{b_K}=R^{\alpha+o(1)}\).  Even (3) becomes only

   \[
   10^{b_K}|\Delta_K|\ll
      R^{0.930676558\ldots}\log R,                                           \tag{5}
   \]

   whose right side grows.  The unconditional right side in (2), after the
   same scaling, also grows because a positive multiple of \(\log R\)
   dominates \((\log R)^{3/5}\).  Thus known cancellation does not certify
   even the \(s=0\) post-transient phase, much less \(s=cR\).
3. There is a sharper special-product identity.  With

   \[
   U_K=\prod_{p\in\mathcal P_K}(p+\epsilon_p),\qquad
   V_K=\prod_{p\in\mathcal P_K}(p-\epsilon_p),                               \tag{6}
   \]

   one has

   \[
   \left|\Delta_K-{1\over2}\log{U_K\over V_K}\right|
   \le \sum_{p\in\mathcal P_K}{1\over3p(p^2-1)}
   =O\!\left({1\over R^2\log R}\right).                                    \tag{7}
   \]

   Consequently the log product still shadows
   \(10^{b_K+s}\Delta_K\) uniformly for

   \[
     0\le s\le
     (2-\alpha)\log_{10}R
     =0.569323441\ldots\log_{10}R,                                          \tag{8}
   \]

   with error \(O(1/\log R)\).  This is a genuine improvement over (2)--(3),
   but its transferable range is logarithmic, not linear.
4. The exact update in \(K\) is a sparse prime-driven walk.  The finite replay
   has many exact plateaus, while each nonzero step depends on three moving
   primality tests.
   Neither the ordinary large sieve nor zero-density averaging supplies the
   high-frequency Weyl estimate that the observed phase distribution would
   require.

## 1. Normalized target and exact phase question

The canonical target remains

\[
 \forall\ell\ge0\ \forall c<10^\ell\ \exists j\ge0:\quad
 \left\lfloor10^\ell\{10^j\pi\}\right\rfloor=c.                            \tag{V1}
\]

The code \(c\) is padded to length \(\ell\); leading zeroes count; occurrence
is contiguous; and \(\ell=0\) is trivial.  The quantifier relevant to this
note is not merely whether \(\Delta_K\to0\).  The global CRT formula requires
control of

\[
 \left\{10^{b_K+s}\Delta_K\right\},
 \qquad 0\le s\le cR,                                                        \tag{9}
\]

the associated modular \(21^{-1}\) lift branch, and the correlated
complementary CRT coordinate.  A bound on \(|\Delta_K|\) is useful only if it
remains below the desired circle scale after multiplication by
\(10^{b_K+s}\).

For all sufficiently large \(K\), the exclusions \(p\le7\) and \(p=17\) lie
below \(R/2\).  They are retained in definitions and computation so that no
small endpoint is silently changed.

## 2. Exact Abel transform

For \(K\ge8\), equivalently \(R>34\), every excluded prime is below the open
lower endpoint.  Define the twisted Chebyshev function

\[
 \vartheta_\chi(x)=\sum_{p\le x}\chi_4(p)\log p
 =\vartheta(x;4,1)-\vartheta(x;4,3).                                        \tag{10}
\]

Stieltjes integration by parts, with the lower endpoint open, then gives
exactly

\[
\begin{split}
 \Delta_K={}&{\vartheta_\chi(R)\over R\log R}
 -{\vartheta_\chi(R/2)\over (R/2)\log(R/2)}\\
 &+\int_{R/2}^{R}
   {\vartheta_\chi(t)(\log t+1)\over t^2(\log t)^2}\,dt .                  \tag{11}
\end{split}
\]

For \(K<8\), (11) needs the evident finite correction for excluded primes;
none of the asymptotic or explicit applications below uses that range.  Formula
(11) makes the scale loss transparent.  Any pointwise estimate
\(|\vartheta_\chi(t)|\le E(t)\) on \([R/2,R]\) can be inserted in (11), but
the resulting estimate is still multiplied by \(10^{b_K+s}\) in (9).

## 3. Fully explicit unconditional bound

Bennett--Martin--O'Bryant--Rechnitzer, Theorem 1.2 and the displayed
\(q=4\) row, give

\[
 \left|\vartheta(x;4,a)-{x\over2}\right|
 <0.0004822{x\over\log x}
 \quad(a=1,3),\quad x\ge4,800,162,889.                                      \tag{12}
\]

Therefore

\[
 |\vartheta_\chi(x)|<c_4{x\over\log x},\qquad c_4=0.0009644.                \tag{13}
\]

Put \(L=\log R\) and \(L_0=\log(R/2)\).  Inserting (13) into (11) and
integrating the two elementary terms gives, for
\(R\ge9,600,325,778\),

\[
 \boxed{
 |\Delta_K|<c_4\left(
 {1\over L_0}-{1\over L}
 +{1\over2L^2}+{3\over2L_0^2}
 \right).}                                                                 \tag{14}
\]

At the left endpoint, the right side is
\(5.128429860\times10^{-6}\).  Here \(b_K=14\), so multiplying the certified
bound by \(10^{b_K}\) gives

\[
 5.128429860\times10^8,                                                      \tag{15}
\]

already completely vacuous modulo one.  The exact universal constants
\(c_\vartheta(q)\le1/840\), \(x\ge8\cdot10^9\) from the same theorem give a
slightly weaker but independent version of (14).

For asymptotic strength, Thorner--Zaman, Corollary 1.4, supplies the current
Vinogradov--Korobov-shaped effective error term for primes in arithmetic
progressions.  For \(q=4\) there is no exceptional real zero: for real
\(s>0\),

\[
 L(s,\chi_4)=\sum_{n\ge0}
 \big((4n+1)^{-s}-(4n+3)^{-s}\big)>0.                                      \tag{16}
\]

Taking the difference of the \(a=1\) and \(a=3\) formulas therefore yields

\[
 \vartheta_\chi(x)\ll
 x\exp\!\left(-c{(\log x)^{3/5}\over(\log\log x)^{1/5}}\right),             \tag{17}
\]

with effective constants.  Equation (2) follows from (11).  Khale's explicit
Vinogradov--Korobov zero-free region gives, for \(|t|\ge10\),

\[
 \Re s\ge1-
 {1\over10.5\log q+61.5(\log|t|)^{2/3}(\log\log|t|)^{1/3}},                 \tag{18}
\]

and corroborates the exact zero-free shape behind (17).  Optimizing constants
inside (11) cannot change the decisive \(3/5\) exponent.

## 4. Fully explicit GRH bound

Assume GRH for Dirichlet \(L\)-functions.  Lee's Corollary 4.4, specialized to
the nonprincipal character modulo \(4\), with \(x_0=e^{10}\), gives after
dropping its favorable negative constant term

\[
 |\vartheta_\chi(t)|\le\sqrt t\,M(\log t),\qquad t\ge e^{10},               \tag{19}
\]

where

\[
 M(y)={y^2\over8\pi}
 +\left({\log4\over2\pi}+9.17523\right)y+0.78834.                          \tag{20}
\]

Since \(M\) is increasing, (11) gives the simple explicit consequence

\[
 \boxed{
 |\Delta_K|\le {M(L)\over\sqrt R}
 \left({3\sqrt2-1\over L_0}
       +{2(\sqrt2-1)\over L_0^2}\right),
 \qquad R\ge2e^{10}.}                                                       \tag{21}
\]

At \(R=2e^{10}\), its right side is
\(1.676452254\times10^{-1}\).  The corresponding \(b_K=6\) shift makes the
right side \(1.676452254\times10^5\).  Asymptotically, (21) is (3), and (5)
follows from

\[
 {R^\alpha\over10}<10^{\lfloor\log_5R\rfloor}\le R^\alpha.                 \tag{22}
\]

Thus even bare GRH is far from a small post-transient phase estimate.  A
square-root-scale theorem would need an additional factor
\(R^{-0.930676\ldots}\), not a better logarithm.

## 5. The symmetric product is substantially sharper

Define the integer polynomial

\[
 F_K(X)=\prod_{p\in\mathcal P_K}(p+\epsilon_pX).                             \tag{23}
\]

Then

\[
 F_K(0)=G_K,\qquad F'_K(0)=S_K,
 \qquad {F'_K(0)\over F_K(0)}=\Delta_K.                                    \tag{24}
\]

The symmetric values \(F_K(1)=U_K\), \(F_K(-1)=V_K\) cancel every even
Taylor moment.  Indeed,

\[
 {1\over2}\log{U_K\over V_K}
 =\sum_{p\in\mathcal P_K}\operatorname{atanh}{\epsilon_p\over p}
 =\Delta_K+
 \sum_{p\in\mathcal P_K}\sum_{j\ge1}
 {\epsilon_p\over(2j+1)p^{2j+1}}.                                         \tag{25}
\]

The absolutely convergent tail satisfies

\[
 \sum_{j\ge1}{1\over(2j+1)p^{2j+1}}
 \le {1\over3p^3(1-p^{-2})}
 ={1\over3p(p^2-1)},                                                       \tag{26}
\]

which proves (7).  The prime number theorem gives
\(\#\mathcal P_K=O(R/\log R)\), hence the final order in (7).  Combining
(7), (22), and \(10^s\le R^{2-\alpha}\) proves (8).

There is additional exact arithmetic structure:

\[
 v_2(U_K)=\#\mathcal P_K,\qquad
 v_2(V_K)\ge2\#\mathcal P_K,\qquad
 S_K\equiv(\#\mathcal P_K)G_K\pmod4.                                      \tag{27}
\]

For the first two assertions, \(p+\epsilon_p\equiv2\pmod4\), whereas
\(p-\epsilon_p\equiv0\pmod4\).  For the third, every summand
\(\epsilon_pG_K/p\) is congruent to \(G_K\pmod4\).  These constraints are
exact, but they are small-adic information; they do not place the real
fractional part in (9).

One can continue (25) to arbitrary fixed order:

\[
 \Delta_K={1\over2}\log{U_K\over V_K}
 -\sum_{j=1}^{J}{1\over2j+1}
   \sum_{p\in\mathcal P_K}{\epsilon_p\over p^{2j+1}}
 +O\!\left({R^{-2J-2}\over\log R}\right).                                 \tag{28}
\]

Every fixed \(J\) still transfers only \(O(\log R)\) orbit steps.  To make
the remainder survive multiplication by \(10^{cR}\), one needs
\(J=\Theta(R/\log R)\), which reconstructs essentially all of the original
rational phase rather than producing a short special-value formula.

## 6. Exact sparse recurrence and why averaging does not close it

Increasing \(K\) by one changes the window from
\((2K+3/2,4K+3]\) to \((2K+7/2,4K+7]\).  With
\(I(n)=1\) when \(n\) is an eligible prime and \(0\) otherwise, one obtains
the exact recurrence

\[
 \boxed{
 \Delta_{K+1}-\Delta_K=
 {I(4K+5)\over4K+5}-{I(4K+7)\over4K+7}
 +{(-1)^KI(2K+3)\over2K+3}.}                                               \tag{29}
\]

This explains both the finite near-uniformity and the analytic obstruction.
On intervals where \(b_K=b\), put

\[
 z_K=e(10^b\Delta_K),\qquad e(x)=e^{2\pi ix}.
\]

Then (29) makes \(z_K\) a multiplicative walk whose sparse increments are
three moving prime indicators.  It is not a polynomial phase or a sum of
independent variables.

The Montgomery--Vaughan large sieve requires a family of separated
frequencies.  Here many adjacent frequencies are exactly equal whenever all
three indicators in (29) vanish.  If a step is nonzero, its denominator is at
most
\((4K+5)(4K+7)(2K+3)=O(R^3)\), so the elementary guaranteed circular
separation after multiplication by \(10^b\) is only \(\gg R^{-3}\).  Even if
that adjacent bound extended to all distinct pairs, inserting only this
guaranteed scale into \(N+\delta^{-1}\) would give an \(O(R^3)\) large-sieve
bound while there are only \(N=O(R)\) values of \(K\).  It does not extend:
nonadjacent accumulated frequencies can be much closer, and exact duplicates
make the ungrouped separation zero.  This route gives no cancellation.

Zero-density theorems average zeros over characters or moduli.  In (1) the
character is the single fixed \(\chi_4\); changing \(K\) changes only the
endpoints.  A zero of \(L(s,\chi_4)\) contributes coherently throughout the
entire \(K\)-average, so a character-family zero-density estimate does not
create an extra power of \(R\).  Abel summation already extracts all that the
known pointwise prime-number theorem supplies.

## 7. What prime-race theory predicts, and what it does not prove here

Rubinstein--Sarnak prove limiting-distribution results for normalized prime
races, under GRH, with their linear-independence hypothesis used for the
strongest regularity and bias conclusions.  Their explicit-formula machinery
suggests a precise adaptation to (1).  Put

\[
 E(y)=y e^{-y/2}\sum_{p\le e^y}\chi_4(p),\qquad
 Z(y)=y e^{y/2}\Delta(e^y).                                                 \tag{30}
\]

Here \(\Delta(x)=\sum_{x/2<p\le x}\chi_4(p)/p\), without the irrelevant
finite eligibility exclusions.  Abel summation gives the exact identity

\[
\begin{split}
 Z(y)={}&E(y)-\sqrt2\,{y\over y-\log2}E(y-\log2)\\
 &+\int_{1/2}^{1}{y\over y+\log u}\,
 u^{-3/2}E(y+\log u)\,du .                                                \tag{31a}
\end{split}
\]

Formally replacing the two slowly varying ratios by one gives, at the
limiting-distribution scale,

\[
 Z(y)=E(y)-\sqrt2E(y-\log2)
 +\int_{1/2}^{1}u^{-3/2}E(y+\log u)\,du+o(1).                              \tag{31}
\]

For a zero frequency \(e^{i\gamma y}\), the multiplier in (31) is

\[
 m(\gamma)=
 (1-\sqrt2e^{-i\gamma\log2})
 {1/2+i\gamma\over-1/2+i\gamma},                                          \tag{32}
\]

so

\[
 |m(\gamma)|=|1-\sqrt2e^{-i\gamma\log2}|
 \ge\sqrt2-1.                                                              \tag{33}
\]

Thus the limiting dyadic reciprocal filter kills no zero frequency.  A full
endpoint and limiting-distribution audit justifying the \(o(1)\) passage from
(31a) to (31) is a clean theorem-sized next target; at present (31)--(33) are
a `proof sketch`.  Under GRH plus linear independence they predict the
distributional scale

\[
 {1\over\sqrt R\log R}                                                     \tag{34}
\]

not the vastly smaller \(R^{-\alpha}\) required merely to keep the
post-transient phase near zero.  Even a rigorous fixed-frequency limiting
distribution would not prove the needed moving-frequency statement, because
the relevant Fourier frequency is \(10^b/(\sqrt R\log R)\to\infty\).

## 8. Denominator period versus interval location

The ordinary prime number theorem gives

\[
 \log G_K=\vartheta(R)-\vartheta(R/2)
 ={R\over2}+o(R).                                                           \tag{35}
\]

Since \((S_K,G_K)=1\) and \((10,G_K)=1\), the decimal orbit of
\(S_K/G_K\) has period \(d_K=\operatorname{ord}_{G_K}(10)\).  The elementary
divisibility \(G_K\mid10^{d_K}-1\) implies

\[
 d_K\ge\log_{10}(G_K+1)
 ={R\over2\log10}+o(R)
 =0.217147240\ldots R+o(R).                                                 \tag{36}
\]

The Hutton bracket has a nominal decimal scale
\((\log_{10}3)R=0.477121254\ldots R\), so (36) is a real linear-period
lower bound within the same order of magnitude.  A lower bound on period,
however, says nothing about discrepancy of the orbit segment.  A cyclic set
of \(O(R)\) points can avoid a fixed interval, and the complementary CRT
coordinate from the global report is still correlated with the same power of
\(10\).

## 9. Finite replay and falsification

The companion checker is
[`hutton_prime_character_phase_check.py`](hutton_prime_character_phase_check.py).
Run it from the repository root:

```text
python3 work/ultrapi-resume/hutton_prime_character_phase_check.py
```

The 2026-08-12 run reported:

```text
source sha256: 2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
exact phase/polynomial/recurrence groups: 599
finite symmetric-log inequalities checked: 599
fixed affine, six-periodic, and K-mod-m event rules: falsified
explicit unconditional endpoint: Delta bound=5.128429860e-06, 10^b bound=5.128429860e+08
explicit GRH endpoint:          Delta bound=1.676452254e-01, 10^b bound=1.676452254e+05
experiment b=7: K-count=78125, adjacent repeats=43432, 20-bin counts=[4132, 4090, 3896, 3762, 3761, 3813, 4239, 3594, 3747, 3956, 3765, 3774, 3970, 3817, 3879, 3828, 4086, 4008, 3891, 4117], star-discrepancy=0.00675765
experiment b=8: K-count=390625, adjacent repeats=235356, 20-bin counts=[19186, 19362, 20320, 20331, 19840, 20188, 18428, 19827, 19566, 18830, 18896, 19892, 18152, 19339, 19603, 20124, 19064, 20235, 19251, 20191], star-discrepancy=0.00539302
experiment isolated Delta-orbit two-digit coverage (c=0.4):
  K= 100 R= 403 starts= 162 distinct-cells= 79
  K= 200 R= 803 starts= 322 distinct-cells= 93
  K= 400 R=1603 starts= 642 distinct-cells=100
  K= 800 R=3203 starts=1282 distinct-cells=100
all exact checks passed; distribution rows are experiments only
```

The exact assertions use integers and `Fraction`: (1), (23)--(24), (27),
(29), and coprimality.  The evaluations of the explicit formulas, log
comparisons, and distribution rows use floating point and have only
`experiment` status.
The near-uniform histograms and two-digit coverage do not include the
complementary CRT coordinate and are not decimal-cylinder certificates.

The recurrence replay also supplies exact counterexamples to:

- a fixed affine first-order recurrence for \(\Delta_K\);
- six-periodicity; and
- any rule making the three prime-event indicators depend only on
  \(K\bmod m\), for every \(1\le m\le64\) in the tested range.

Finite falsification does not rule out a deeper recurrence.

For the affine claim, the explicit witnesses are

\[
 \Delta_7=\Delta_8=-{36884\over392863},\qquad
 \Delta_{11}=\Delta_{12}={25107806\over2756205443},                         \tag{40}
\]

two distinct plateaus, together with
\(\Delta_2=-1/11\ne-2/143=\Delta_3\).  Two distinct plateaus in an identity
\(x_{K+1}=ax_K+c\) force \(a=1,c=0\), contradicted by the last pair.

## 10. Primary-source audit

The bounded search used only primary papers for external theorems.

1. Michael A. Bennett, Greg Martin, Kevin O'Bryant, and Andrew Rechnitzer,
   [*Explicit bounds for primes in arithmetic progressions*](https://arxiv.org/abs/1802.00085),
   arXiv:1802.00085v3, Theorems 1.1--1.3 and the \(q=4\) table.  Downloaded
   PDF SHA-256:
   `e51f8b8f63486c2259efe076d367504f08dda0fe9e99dc35bf36de544ffc0601`.
2. Ethan Simpson Lee,
   [*The prime number theorem for primes in arithmetic progressions at large values*](https://arxiv.org/abs/2301.13457),
   arXiv:2301.13457v2, Theorem 4.2, Corollary 4.4, and Table 5.  Downloaded
   PDF SHA-256:
   `d36de57c5bdaad1470f318dc7423cde1ae234e7348a8edaa01f7c683d115f4cc`.
3. Jesse Thorner and Asif Zaman,
   [*Refinements to the prime number theorem for arithmetic progressions*](https://arxiv.org/abs/2108.10878),
   arXiv:2108.10878v2, Theorem 1.1 and Corollary 1.4.  Downloaded PDF SHA-256:
   `588ec896e0820c3620175b25da58850efbefc67b71227acac1d5c3fa4f6b3b09`.
4. Tanmay Khale,
   [*An explicit Vinogradov--Korobov zero-free region for Dirichlet L-functions*](https://arxiv.org/abs/2210.06457),
   arXiv:2210.06457v1, Theorem 1.1.  Downloaded PDF SHA-256:
   `e232e295f93e4b3be4e33d4a0043145645832316fd765fde89eadfc7b735c136`.
5. Michael Rubinstein and Peter Sarnak,
   [*Chebyshev's Bias*](https://doi.org/10.1080/10586458.1994.10504289),
   *Experimental Mathematics* 3 (1994), 173--197.  Their limiting-distribution
   framework is cited only for the conditional research direction in Section
   7; the weighted dyadic adaptation is not attributed to them as a proved
   theorem.
6. H. L. Montgomery and R. C. Vaughan,
   [*The large sieve*](https://doi.org/10.1112/S0025579300004708),
   *Mathematika* 20 (1973), 119--134.  Its separation hypothesis and
   \(N+\delta^{-1}\) scale are used only to audit applicability in Section 6.

This search found no primary theorem controlling

\[
 {1\over\#\mathcal K_b}
 \sum_{K\in\mathcal K_b}
 e\!\left(h10^b\Delta_K\right),\qquad
 \mathcal K_b=\{K:5^b\le4K+3<5^{b+1}\},                                  \tag{37}
\]

uniformly for fixed nonzero \(h\), let alone for the frequencies and joint CRT
state required by V1.

## 11. Strongest theorem-sized next target and exact barrier

The observed finite distribution of the real reciprocal-sum proxy is captured
by the precise `conjecture`

\[
 \boxed{
 {1\over\#\mathcal K_b}
 \sum_{K\in\mathcal K_b}e(h10^b\Delta_K)\longrightarrow0
 \quad(b\to\infty),\qquad h\in\mathbb Z\setminus\{0\}.}                    \tag{38}
\]

By Weyl's criterion, (38) would prove equidistribution of
\(\{10^{b_K}\Delta_K\}\) across \(K\).  It would **not by itself** prove
equidistribution of the actual isolated \(G_K\)-coordinate.  Indeed, if

\[
 u_K\equiv68\,21^{-1}S_K\pmod {G_K},\qquad 0\le u_K<G_K,
\]

then for an integer \(n_K\),

\[
 {u_K\over G_K}={n_K\over21}+{68\over21}\Delta_K.
\]

Thus modular division by \(21\) selects one of 21 correlated lift branches;
equidistribution after the map \(y\mapsto21y\) does not imply
equidistribution of a selected inverse branch.  The exact stronger isolated
coordinate target is

\[
 {1\over\#\mathcal K_b}\sum_{K\in\mathcal K_b}
 e\!\left(h10^b{u_K\over G_K}\right)\longrightarrow0
 \quad(b\to\infty),\qquad h\in\mathbb Z\setminus\{0\}.                    \tag{38'}
\]

A clean intermediate target is to turn (31)--(33) into a rigorous
GRH-plus-linear-independence limiting distribution for
\(\sqrt R\log R\,\Delta_K\), with its mean and variance written explicitly in
terms of the zeros of \(L(s,\chi_4)\).  That target is strictly weaker than
even (38): ordinary weak convergence controls fixed Fourier frequencies,
whereas (38) samples a frequency growing like
\(R^{0.930676\ldots}/\log R\) on the natural prime-race scale.

Even (38') would still not prove V1.  Write
\(B_K^{\rm CRT}=Q_K/(5^{b_K}G_K)\) for the complementary modulus from the
global CRT report and \(e_M(x)=\exp(2\pi ix/M)\).  The full phase is

\[
 e_{G_K}\!\left({68\over21}10^{b_K+s}S_K\right)
 e_{B_K^{\rm CRT}}(\beta_{K,s}),                                             \tag{39}
\]

and the second factor is correlated with the first.  The exact remaining
V1-level target is a joint moving-frequency estimate for (39), or a direct
full-residue cylinder hit within \(s\le(\log_{10}3+o(1))R\).

**Bottom line:** the signed prime sum has substantially more structure than
the triangle bound reveals.  Its best unconditional and GRH pointwise bounds,
its exact sparse recurrence, its symmetric log product, and its linear decimal
period can all be made explicit.  The log product is accurate through a new
\(0.569323\ldots\log_{10}R\) post-transient window, and finite phase data look
well distributed.  None controls the moving frequency for \(O(R)\) steps or
the correlated full CRT state.  No complete proof of V1 follows.
