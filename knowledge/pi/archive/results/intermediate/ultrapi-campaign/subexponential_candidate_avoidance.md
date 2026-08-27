# Subexponential candidates versus forbidden-word avoidance

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: Marcel's immutable local question contains no external source
URL, so none is invented here.  
Route: the complementary quotient in
[`actual_numerator_phase_attack.md`](actual_numerator_phase_attack.md), the
general high-prime theorem in
[`general_seed_band_attack.md`](general_seed_band_attack.md), and the exact
carry recurrence recorded there.

## Outcome and exact status

No complete proof that every finite decimal word occurs in \(\pi\) was
obtained. The canonical target remains a `conjecture`.

There is a material obstruction to a tempting entropy argument. Freezing the
known Machin denominator components leaves only

\[
                         D_j=\exp(o(j))
\]

coarse quotient candidates. If a fixed word \(w\) were missing, a pulse of
length \(T=\Theta(j)\) would have to lie in a word-avoidance set of measure
\(\exp(-\delta_wT+o(T))\). Multiplying these two quantities gives \(o(1)\),
but that product is only the **zero-mode or random-shift expectation**. It is
not a deterministic upper bound for the one arithmetic shifted grid selected
by the Machin numerator.

The exact deterministic grid bound has an additive boundary term, one per
avoidance cylinder (or one per merged component). That term is exponential,
not \(o(1)\). It cannot simply be discarded: an explicit reduced rational
family with complementary modulus \(D=81\) has at least one avoiding member
through an arbitrarily long pulse, and an exact finite run finds 21 reduced
zero-avoiding members even when the zero-mode main term is
\(5.7\times10^{-8}\). The same family has completely known fine carries and
can be made compatible across indices with a positive summable geometric
forcing.

This is a `proof sketch` separator for candidate counting, grid discrepancy,
and nonautonomous-carry arguments based only on the currently available
structural data. It is not a counterexample involving the actual Machin
numerator and says nothing against V1. A successful continuation needs a
shift-specific resonant estimate for the **actual** Machin remainder, or an
equivalent theorem selecting its coarse quotient.

## 1. Normalized target and the candidate set

The canonical V1 statement is

\[
 \forall m\in\mathbb N\;\forall w\in\{0,\ldots,9\}^{m}\;
 \exists n\in\mathbb N:\quad
 (d_n(\pi),\ldots,d_{n+m-1}(\pi))=w.               \tag{1}
\]

Digits are after the decimal point, leading zeroes in \(w\) are allowed, and
\(m=0\) is vacuous. The target is contiguous occurrence, not subsequence
occurrence and not normality.

At one exact rational Machin seed, write

\[
 x={b\over Q},\qquad Q=FD,\qquad (F,D)=1,
 \qquad b=Fc+r,\quad0\le r<F.                      \tag{2}
\]

The local calculations determine \(r=b\bmod F\), while \(c\) ranges over at
most \(D\) possibilities. Before a coprimality restriction, the full shifted
grid is

\[
 G(D,r/F)=\left\{{c\over D}+{r\over FD}:0\le c<D\right\}
 \subset[0,1).                                     \tag{3}
\]

The actual reduced numerator is one member of this grid. Enlarging (3) by
including nonreduced alternatives only makes any desired upper bound harder;
the explicit separator below nevertheless uses a reduced member.

Fix a nonempty word \(w\) of length \(m\), and ask for avoidance at the
\(T\) starts \(0,\ldots,T-1\). Put \(n=T+m-1\). Let \(A_w(n)\) be the set of
length-\(n\) decimal strings containing no copy of \(w\), and let
\(a_w(n)=|A_w(n)|\). With the half-open floor convention, the survivor set is
exactly

\[
 U_{w,T}=\bigcup_{k\in A_w(n)}
       \left[{k\over10^n},{k+1\over10^n}\right).   \tag{4}
\]

This convention handles terminating endpoints without choosing between two
decimal expansions. The finite avoidance automaton gives

\[
 a_w(n)=\exp(n\log\lambda_w+o(n)),
 \qquad \lambda_w<10,                              \tag{5}
\]

or the weaker sufficient upper bound
\(a_w(n)=O_w(n^{m-1}\lambda_w^n)\). Hence

\[
 \mu(U_{w,T})={a_w(n)\over10^n}
              =\exp(-\delta_wn+o(n)),
 \qquad\delta_w=\log(10/\lambda_w)>0.              \tag{6}
\]

If \(\log D=o(T)\), then indeed

\[
                         D\,\mu(U_{w,T})=o(1).      \tag{7}
\]

Equation (7) is correct. Interpreting it as the number of candidates in
\(U_{w,T}\) is the error.

In fact its probabilistic meaning is exact. If the shift \(\alpha\) is
uniform on one fundamental interval \([0,1/D)\), then Tonelli's theorem and
the partition of \([0,1)\) into the \(D\) grid cells give

\[
 D\int_0^{1/D}
   \#\{0\le c<D:c/D+\alpha\in U_{w,T}\}\,d\alpha
   =D\mu(U_{w,T}).                                  \tag{7a}
\]

Thus (7) says that almost every shift misses the survivor set at this scale.
It supplies no conclusion for the one deterministic shift
\(\alpha=r/(FD)\).

## 2. Exact grid count and the fatal boundary term

Every half-open interval of length \(10^{-n}\) contains at most

\[
                         {D\over10^n}+1             \tag{8}
\]

points of the shifted \(D\)-grid. Therefore the deterministic count

\[
 N(D,r;w,T):=|G(D,r/F)\cap U_{w,T}|
\]

satisfies only

\[
 \boxed{
 N(D,r;w,T)
 \le D\,{a_w(n)\over10^n}+a_w(n).}                 \tag{9}
\]

The first summand is (7). The second is
\(\exp(n\log\lambda_w+o(n))\), so it overwhelms the desired \(<1\) bound.
Merging adjacent cylinders changes the second term to the number \(R_w(n)\)
of connected components of (4), but this is still generally exponential:

\[
                         N\le D\mu(U_{w,T})+R_w(n). \tag{10}
\]

For the one-digit word \(w=0\), the calculation is completely explicit:

\[
 a_0(n)=9^n,qquad R_0(n)=9^{n-1}.                 \tag{11}
\]

Indeed, for each zero-free prefix of length \(n-1\), the allowed final
digits \(1,\ldots,9\) merge into one run, and the intervening final zero
separates consecutive runs. Thus even optimal interval merging leaves an
exponential boundary discrepancy.

The logical issue is equally sharp. Under the hypothesis that \(w\) is
missing and after a valid shadow transfer, the actual quotient itself gives

\[
                         N(D_j,r_j;w,T_j)\ge1.      \tag{12}
\]

To get a contradiction one must prove \(N=0\) for some \(j\). A small
average, a density-zero exceptional set of shifts, or even the exact bound
\(N\le1\) does not contradict (12). The actual arithmetic shift may be the
unique exceptional hit.

Half-open endpoints do not rescue (9): they assign every endpoint to one
cell and leave the additive term. There is also a separate shadow-boundary
obligation when transferring avoidance from \(\pi\) to a rational Machin
approximant. Even granting that transfer exactly, (9)--(12) remain an
obstruction.

## 3. An exact reduced separator for every fixed word

The boundary term is not merely a crude proof artifact. Let \(w\) be any
nonempty word of length \(m\). Choose

\[
 a\in\{1,\ldots,8\}\quad\text{with}\quad w\ne a^m. \tag{13}
\]

Such an \(a\) always exists. Set

\[
 D=81,qquad F=(5\cdot239)^S,qquad Q=FD,
\]

and define

\[
 b=9aF-1,qquad
 x={b\over Q}={a\over9}-{1\over81F}.               \tag{14}
\]

This displayed fraction is reduced. Modulo \(F\), its numerator is \(-1\);
modulo 3, it is also \(-1\). Hence \((b,81F)=1\). Its exact quotient split
is

\[
 b=F(9a-1)+(F-1),qquad c=9a-1,quad r=F-1.         \tag{15}
\]

Take the carry recurrence from the actual-numerator report:

\[
\begin{aligned}
 r_{t+1}&=10r_t-F\kappa_t,\\
 c_{t+1}&=10c_t+\kappa_t-D\delta_t,\\
 \delta_t&=\left\lfloor{10c_t+\kappa_t\over D}\right\rfloor.
\end{aligned}                                      \tag{16}
\]

For every \(t\) with \(10^{t+1}<F\), direct induction gives

\[
 r_t=F-10^t,qquad \kappa_t=9,qquad
 c_t=9a-1,qquad\delta_t=a.                        \tag{17}
\]

The coarse-state calculation is

\[
 10(9a-1)+9=90a-1,quad
 \left\lfloor{90a-1\over81}\right\rfloor=a,quad
 (90a-1)-81a=9a-1.                                \tag{18}
\]

Consequently, if \(F>10^{T+m-1}\), the first \(T+m-1\) digits of \(x\)
are all \(a\), so none of the first \(T\) length-\(m\) blocks equals \(w\).
The complementary candidate count is the constant

\[
                         D=81=\exp(o(T)).           \tag{19}
\]

Thus a completely known fine carry can lock the coarse quotient into an
avoiding periodic state. It does not act as an independent random input.

The separator can also be made cross-index consistent. Fix an integer
\(A=(5\cdot239)^K>1\), put \(F_j=A^{j+1}\), and let

\[
 x_j={a\over9}-{1\over81F_j},qquad
 \Delta_j={10\over81F_j}-{1\over81F_{j+1}}>0.      \tag{20}
\]

Then exactly

\[
                    x_{j+1}=\{10x_j+\Delta_j\}.    \tag{21}
\]

The forcing \(\Delta_j\) is positive, geometric, and summable. Choosing
\(\log_{10}A\) larger than the desired pulse coefficient makes (17) avoid
\(w\) for \(T_j=\Theta(j)\) at every large index. Hence subexponential
candidate count, exact reduced denominators, large 5/239-primary frozen
factors, known fine carries, a powers-of-ten recurrence, and positive
summable forcing are jointly insufficient.

Equations (13)--(21) are a separator for those premises, not for the exact
Machin residue or exact Machin forcing. Any successful theorem is free to
use their special arithmetic values; it now has to do so essentially.

## 4. Why multiplying probabilities across indices is invalid

One might try to multiply the exponentially small proportions in (6) over
many indices. That introduces an independence statement which is absent.
The blocks at nearby indices overlap, and the quotient states are
synchronised by (16), not resampled. The family (20)--(21) is an explicit
recurrence-consistent exceptional chain: the same constant itinerary
survives at every index despite \(D_j=81\).

More abstractly, a pointwise list of \(\exp(o(j))\) candidates may contain one
distinguished path through a finite-state avoidance automaton forever. State
count controls neither which path is selected nor its entropy. Counting the
Cartesian product of the lists and assigning a random-word probability to
each tuple silently treats incompatible deterministic carries as independent
samples.

The companion
[`cross_index_quotient_attack.md`](cross_index_quotient_attack.md) goes
further for the exact Machin denominators: it identifies the consistent
candidate family by a gcd of complementary moduli and finds a persistent
3-primary subgroup. The simpler construction above isolates the distinct
automata/grid-counting error without relying on that extra arithmetic.

## 5. Reproducible exact checks (`experiment`)

[`subexponential_candidate_avoidance_check.py`](subexponential_candidate_avoidance_check.py)
uses only integers and `Fraction`; it neither evaluates \(\pi\) nor reads a
digit table. Its SHA-256 is
`1b82ef984a4ef1ff9300a472b2995a5f0e49caf7950e03a69d029685ef3581bb`.

Commands:

```bash
python3 -m py_compile \
  work/ultrapi-resume/subexponential_candidate_avoidance_check.py
python3 work/ultrapi-resume/subexponential_candidate_avoidance_check.py
```

The retained run checks the shifted \(81\)-grid for zero avoidance, the exact
fine/coarse carries for four representative missing words, and the positive
forcing recurrence (20):

```text
claim_status=experiment
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
complementary_modulus=81
zero_avoidance_grid=horizon:10,count:21,reduced_count:21,zero_mode_main:28.2429536481
zero_avoidance_grid=horizon:50,count:21,reduced_count:21,zero_mode_main:0.417455791793
zero_avoidance_grid=horizon:100,count:21,reduced_count:21,zero_mode_main:0.00215147330989
zero_avoidance_grid=horizon:200,count:21,reduced_count:21,zero_mode_main:5.71461407801e-08
constant_itinerary_checks=1600
word_avoidance_checks=1000
reduced_seed_checks=8
fine_and_coarse_carry_checks=1600
positive_forcing_recurrence_checks=160
all exact checks passed
```

The 21 surviving reduced grid points at horizon 200 show an exponential
resonance relative to the zero-mode main term. This is finite evidence only;
the algebraic construction in Section 3, rather than the finite run, is the
general separator.

## 6. The exact missing estimate

For the actual Machin split, write

\[
 \alpha_j={r_j\over F_jD_j},\qquad
 N_{j,w,T}=\#\left\{0\le c<D_j:
 {c\over D_j}+\alpha_j\in U_{w,T}\right\}.         \tag{22}
\]

Since \(D_j\mu(U_{w,T})=o(1)\) at \(T=\Theta(j)\), any one of the following
would be a real bridge:

1. a shift-specific relative bound
   \(N_{j,w,T}\le C_wD_j\mu(U_{w,T})\) for the actual \(\alpha_j\);
2. a resonant Fourier/digital-discrepancy estimate strong enough to give
   \(N_{j,w,T}<1\); or
3. a cross-index theorem proving that the one actual coarse state cannot
   follow the avoidance automaton indefinitely.

Because \(N_{j,w,T}\) is an integer, any such \(<1\) estimate would force
\(N=0\) and contradict a transferred missing-word hypothesis. But no bound
of these forms follows uniformly from \(D_j=\exp(o(j))\), from the avoidance
spectral radius, or from known fine carries: Section 3 gives explicit
countermodels to each uniform reading.

In Fourier language, (7) controls only the zero frequency. The unresolved
nonzero frequencies resonant with the denominator grid must cancel for the
specific arithmetic shift \(\alpha_j\). In carry language, the same missing
information is the actual coarse state \(c_j\). Establishing either statement
would no longer be a counting lemma; it would be new fixed-\(\pi\) numerator
distribution.

## Bottom line

The subexponential quotient theorem is meaningful denominator progress, but
it does not combine with forbidden-word entropy by a first-moment argument.
The union-of-cylinders boundary term is exponentially large and is genuinely
realized by resonant reduced grids. Nonautonomous fine carries can preserve,
rather than destroy, an avoiding itinerary. The remaining obligation is an
actual-shift discrepancy/cancellation theorem or an equivalent archimedean
selection of the true quotient. No cylinder hit, candidate resolution, or
verified resolution follows here.
