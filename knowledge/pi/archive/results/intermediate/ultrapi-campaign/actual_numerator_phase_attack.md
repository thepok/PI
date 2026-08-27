# Actual complementary-numerator phase: exact quotient obstruction

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Provenance: the immutable local source records Marcel's 2026-07-21
question; it contains no external source URL, so none is invented here.  
Route: equation (11w) of [`ultrapi.md`](../../ultrapi.md),
[`fixed_modulus_attack.md`](fixed_modulus_attack.md),
[`multiprime_adversarial.md`](multiprime_adversarial.md), and the local
T49--T51 endpoint/fixed-band developments.

## Outcome and exact claim status

No complete proof that every finite decimal word occurs in \(\pi\) was
obtained. The canonical target remains a `conjecture`.

The sharp finding is an exact obstruction concerning the **actual** reduced
numerator, rather than an alternative numerator. Suppose the actual seed has
fractional part

\[
 x={b\over Q},\qquad 0\le b<Q,
\]

and split its actual denominator as \(Q=FD\), with \((F,D)=1\). If all local
Machin calculations determine \(b\bmod F\), write

\[
 r=b\bmod F,\qquad b=Fc+r,\qquad 0\le r<F,\quad0\le c<D. \tag{1}
\]

Then the supposedly complementary numerator is exactly

\[
 \boxed{c=\lfloor Dx\rfloor,\qquad {r\over F}=\{Dx\},qquad
 x={c\over D}+{r\over FD}.}                       \tag{2}
\]

Thus local CRT information determines the fine position **inside** the
actual \(D\)-grid cell, while the undetermined quotient \(c\) is precisely
the archimedean cell containing the actual Machin phase. This is an
unconditional elementary identity, recorded here as a `proof sketch`
because it has not been added to the verified Lean track. It exposes a
circularity: recovering \(c\), bounding its carries, or proving cancellation
for its powers-of-ten orbit is not a bridge to the digit problem; it is the
remaining digit problem in quotient coordinates.

There is also a positive but strictly weaker advance. The T48/T50/T51 residue
calculation extends uniformly to all high prime bands. An elementary height
argument shows that primes carrying all but \(o(j)\) of the non-base
denominator's logarithmic mass survive in the actual reduced denominator of
the seed \(y_j=10^jM_{3j}\). Consequently, after the complete 5- and
239-primary components and these high-prime components are fixed, only
\(\exp(o(j))\) quotient values \(c\) remain. This is a `proof sketch`; the
PNT estimate used to count the primes is `literature-checked` in the dated
companion reports. It still supplies no information selecting the one actual
quotient.

## 1. Normalized target and quantifiers

The canonical V1 statement is

\[
 \forall L\in\mathbb N\;\forall w\in\{0,\ldots,9\}^{L}\;
 \exists n\in\mathbb N:\quad
 (d_n(\pi),\ldots,d_{n+L-1}(\pi))=w.              \tag{3}
\]

Digits are after the decimal point, leading zeroes in \(w\) are allowed,
and \(L=0\) is vacuous. This is finite contiguous occurrence, not occurrence
of every infinite tail and not the subsequence reading.

All results below concern the one numerator selected by the exact finite
Machin formula. Finite calculations are `experiment`; they are used only to
falsify simpler recurrences and audit signs.

## 2. General high-prime localization

Put

\[
 y_j=10^jM_{3j}={a_j\over Q_j},\qquad d=12j+3,
\]

with \(a_j/Q_j\) reduced. Equation (11w), regrouped as in the companion
reports, gives the exact finite seed expansion

\[
 {y_j\over10^j}=
 \sum_{\substack{1\le u\le d\\u\text{ odd}}}
 {4\chi_4(u)(4\cdot239^u-5^u)\over u5^u239^u}
 -{4\over(d+2)239^{d+2}},                         \tag{4}
\]

where \(\chi_4(u)=(-1)^{(u-1)/2}\).

For \(r\ge1\), define the fixed rational

\[
 C_r:=4\sum_{\substack{1\le m\le2r-1\\m\text{ odd}}}
 {\chi_4(m)\over m}
 \left({4\over5^m}-{1\over239^m}\right).          \tag{5}
\]

This recovers the two constants already isolated locally:

\[
 C_1={4\cdot951\over5\cdot239},\qquad
 C_2={5359397032\over1706489875}.                 \tag{6}
\]

Let \(p\) be an odd prime in the band

\[
 {d\over2r+1}<p\le {d\over2r-1}.                 \tag{7}
\]

The odd multiples of \(p\) occurring in the common sum (4) are exactly
\(p,3p,\ldots,(2r-1)p\). Multiplication by \(p\), multiplicativity of
\(\chi_4\), and Fermat's theorem give the localized identity

\[
 p y_j\equiv10^j\chi_4(p)C_r\pmod p.              \tag{8}
\]

Here rational congruence is in \(\mathbb Z_{(p)}/p\mathbb Z_{(p)}\). The
identity requires \(p\notin\{5,239\}\), \(p\nmid d+2\), and
\(p>2r-1\). If additionally \(C_r\not\equiv0\pmod p\), all other terms are
\(p\)-integral and therefore

\[
 \boxed{v_p(y_j)=-1,\quad p\Vert Q_j.}             \tag{9}
\]

This is the exact general pattern behind T48's upper band, T50's
\(p,3p\) band, and T49's propagated endpoint coefficient. It is a
`proof sketch`, not a new Lean registration.

### Uniform removal of coefficient exceptions

The constants in (5) never vanish as rational numbers. Alternating-series
bounds give, for every \(r\ge1\),

\[
 C_r\ge16\left({1\over5}-{1\over3\cdot5^3}\right)-{4\over239}>0. \tag{10}
\]

Moreover, with

\[
 H_r=(2r-1)!\,5^{2r-1}239^{2r-1},                 \tag{11}
\]

the number \(H_rC_r\) is a positive integer smaller than \(4H_r\). Hence a
prime \(p>4H_r\) cannot cancel (8).

Take, for sufficiently large \(d\),

\[
 R=\left\lfloor{\log d\over16\log\log d}\right\rfloor,
 \qquad B={d\over2R+1}.                           \tag{12}
\]

The elementary bound

\[
 \log(4H_R)\le\log4+2R\log(2R)+2R\log1195
              <\tfrac12\log d                    \tag{13}
\]

holds eventually, whereas \(\log B=(1-o(1))\log d\). Thus every prime

\[
 B<p\le d,qquad p\nmid d+2,                       \tag{14}
\]

falls into one of (7), has nonzero coefficient, and satisfies (9). The
excluded primes in (14) have product at most \(d+2\). By the prime number
theorem,

\[
 \log\!\prod_{\substack{B<p\le d\\p\nmid d+2}}p
   =d-o(d).                                        \tag{15}
\]

So the actual reduced seed denominator contains, to first logarithmic
order, the entire non-base prime radical. This strengthens the fixed
fixed-band picture, but it remains purely local information.

## 3. Almost all CRT components still leave exactly the digit quotient

Let \(P_j\) be the prime product in (15), and let \(5^{s_j}\) and
\(239^{t_j}\) be the complete corresponding primary factors of \(Q_j\).
Put

\[
 F_j=5^{s_j}239^{t_j}P_j,qquad D_j=Q_j/F_j.        \tag{16}
\]

The denominator in (4) shows that every non-base prime power of \(Q_j\)
comes from an odd integer at most \(d+2\). After (14) is removed,

\[
 \log D_j
 \le \pi(B)\log(d+2)+O(\log d)
 =O(B)
 =O\!\left({j\log\log j\over\log j}\right)=o(j). \tag{17}
\]

Here cancellations in the actual reduction can only make \(D_j\) smaller.
Thus all components in (16) restrict the actual numerator to at most

\[
 D_j=\exp(o(j))                                   \tag{18}
\]

possible quotients. The local formula (8), together with the full base
primary residues computable from the exact reverse Taylor recurrence,
determines the remainder \(r_j=b_j\bmod F_j\) explicitly.

This sounds close to an archimedean theorem, but (2) identifies the remaining
choice exactly:

\[
 c_j=\left\lfloor D_j\{y_j\}\right\rfloor.        \tag{19}
\]

The quotient is not a hidden independent CRT variable. It is the coarse
cell index of the actual phase.

For a scale statement with both upper and lower bounds, retain rather than
freeze the certified primes in \((B,3B]\), and freeze only those above
\(3B\). The resulting complementary factor \(D_j^*\) satisfies, by (9) and
PNT,

\[
 \log D_j^*=\Theta(B).                             \tag{20}
\]

Equation (2) then gives

\[
 0\le\{y_j\}-{c_j^*\over D_j^*}<{1\over D_j^*}
   =\exp\!\left[-\Theta\!\left(
       {j\log\log j\over\log j}\right)\right].   \tag{21}
\]

This is an exact statement about the actual numerator, but it is merely the
lower \(D_j^*\)-grid rounding of \(\{y_j\}\). Combining (21) with T38's
Machin shadow gives a rational approximation to \(\pi\) whose error is only
\(q^{-1+o(1)}\) (indeed the leading grid term is \(1/q\)) after division by
\(10^j\). It has no irrationality-measure leverage.

## 4. Exact carry recurrence: the missing quotient generates the digits

The circularity becomes literal along a powers-of-ten orbit. For fixed
\(Q=FD\), put

\[
 b_t=10^tb\bmod Q,\quad
 r_t=b_t\bmod F,\quad b_t=Fc_t+r_t.               \tag{22}
\]

The known local components determine \(r_t\). Define

\[
 \kappa_t=\left\lfloor{10r_t\over F}\right\rfloor,
 \qquad
 \delta_t=\left\lfloor{10b_t\over Q}\right\rfloor. \tag{23}
\]

Then exact Euclidean division gives

\[
\begin{aligned}
 r_{t+1}&=10r_t-F\kappa_t,\\
 c_{t+1}&=10c_t+\kappa_t-D\delta_t,\\
 \delta_t&=\left\lfloor{10c_t+\kappa_t\over D}\right\rfloor.
\end{aligned}                                      \tag{24}
\]

The number \(\delta_t\) is exactly the next decimal digit of \(b_t/Q\).
Thus prime localization supplies the fine carries \(\kappa_t\), but the
digit is the coarse carry of the one unknown actual state \(c_t\). Reversing
(24) from a proposed word simply reconstructs the interval of initial
\(c_0\)'s producing that word. It does not show that the actual \(c_0\) lies
there.

T46's small exact forcing telescope changes (24) by a known small rational
increment over a pulse. T49/T50 enlarge the set of components for which
\(r_t\) is known. Neither changes the role of \(c_0\): it remains the state
whose decimal carries must be controlled.

## 5. CRT product formulas and character sums do not remove the quotient

Choose inverses \(D^{-1}\pmod F\) and \(F^{-1}\pmod D\). Additive CRT gives
the exact factorization

\[
 e_Q(hb_t)=
 e_F\!\left(hb_tD^{-1}\right)
 e_D\!\left(hb_tF^{-1}\right).                   \tag{25}
\]

The first factor is determined by the localized Machin components. From
\(b_t=Fc_t+r_t\), the second is

\[
 e_D\!\left(hc_t+hr_tF^{-1}\right).              \tag{26}
\]

The factor involving \(r_t\) is also known; the remaining factor is exactly
\(e_D(hc_t)\). Therefore separate prime-modulus estimates, a tensor-product
interpretation, or multiplication of local phases cannot bound the full sum

\[
 \sum_{t<T}e_Q(hb_t)                               \tag{27}
\]

without a theorem about the actual quotient orbit \(c_t\). The factors in
(25) have modulus one and are synchronised by the same exponent \(10^t\);
there is no independence inequality. Averaging (26) over \(c_0\bmod D\)
returns to the alternative-numerator separator and says nothing about the
selected seed.

For the range (20), \(D=\exp(\Theta(B))\). A pulse of useful length is only
logarithmic in this modulus. The primary-source searches recorded in the
companion reports found estimates for complete families or polynomial-length
orbits, not for this one selected critical-length quotient orbit. No new
applicable character-sum theorem was found here.

## 6. Exact reversal does not create a closed reduced-numerator recurrence

For either Taylor base, the reverse quantity

\[
 R_q(m)=(-1)^m(2m+1)q^{2m+1}S_q(m)
\]

satisfies

\[
 R_q(m)=1-q^2{2m+1\over2m-1}R_q(m-1).             \tag{28}
\]

This is useful for computing complete 5- and 239-primary components. After
the two bases and all linear denominators are combined and reduced, however,
the gcd cancellation is part of the actual numerator. The reduced
denominators are not nested, so (28) does not descend to a fixed-modulus
recurrence for \(c_j\).

The exact run below found the first losses from \(Q_{j-1}\) to \(Q_j\) at

\[
 (j,\text{lost factor})=(3,11),(5,19),(16,37),(27,317),
 (28,47),(30,11),\ldots                            \tag{29}
\]

This falsifies the simplest reduced-denominator nesting proposal. Returning
to a deliberately unreduced nested LCD restores equation (11x), but then its
numerator contains exactly the same unresolved Euclidean quotient and gcd
cancellation. No new state reduction results.

The stronger claim that every \(C_r\) is a unit modulo every eligible prime
is also false at finite scale. For example, the numerators of \(C_3\) have
prime factors 37 and 79, that of \(C_4\) has factors 47 and 127, and that of
\(C_8\) has factors 89, 127, and 151. The height argument (13), not a false
universal noncancellation rule, is what makes the growing-band result valid.

## 7. Reproducible exact checks (`experiment`)

The script
[`actual_numerator_phase_experiment.py`](actual_numerator_phase_experiment.py),
SHA-256
`d9fcbe540bb148739d836af673451dd62a1cc3e9b0f3704df804c19303229764`,
uses only `Fraction`, integer powers, exact valuations, and modular inverses.
It neither evaluates \(\pi\) nor reads a digit table.

Command:

```bash
python -m py_compile work/ultrapi-resume/actual_numerator_phase_experiment.py
python work/ultrapi-resume/actual_numerator_phase_experiment.py --max-j 80
```

Retained output:

```text
claim_status=experiment
j_range=1..80
general_band_residue_checks=6399
coefficient_cancellations_skipped=121
quotient_and_carry_checks=1600
reduced_denominator_nonnesting_events=12
first_nonnesting_events=[(3, 11), (5, 19), (16, 37), (27, 317), (28, 47), (30, 11), (33, 79), (44, 41)]
all exact checks passed
```

The run checks (8)--(9) whenever the displayed coefficient is a unit, checks
(1)--(2) on the actual reduced numerator, checks every identity in (24) for
twenty steps at every seed, and records rather than hides coefficient
cancellations and denominator nonnesting. Finite success is not evidence for
V1 or for an untested asymptotic.

## 8. Sharp remaining lemma

The local-prime program can be pushed to almost the entire denominator
radical, but that no longer appears to be the load-bearing task. A genuine
next lemma must say something not invariant under replacing the actual
quotient \(c_j\) by another residue. Examples of sufficient new information
would be:

1. a nontrivial discrepancy or exponential-sum bound for the one actual
   quotient orbit in (24), at length comparable to \(\log D_j\);
2. a cross-index recurrence for the reduced quotients \(c_j\) with controlled
   carries that survives the nonnesting in (29); or
3. a direct interval theorem placing the actual \(c_j\), for infinitely many
   suitable \(j\), in every prescribed decimal-cylinder interval.

Merely computing more congruences, increasing \(F_j\), writing (25), or
reversing (28) cannot qualify: by (2) and (24), those operations leave the
desired archimedean carry as the unknown variable.

## Bottom line

The actual numerator has now been isolated more sharply. Generalized Machin
localization controls all but subexponential quotient ambiguity, but exact
Euclidean reciprocity identifies that last quotient with the actual decimal
cell index. The complementary CRT phase is therefore not a technical residue
left after the proof; it is a coordinate copy of the fixed-\(\pi\) digit
problem. No unconditional Weyl cancellation, cylinder hit, candidate
resolution, or verified resolution follows.
