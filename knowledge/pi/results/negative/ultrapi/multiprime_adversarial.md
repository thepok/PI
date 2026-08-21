# Adversarial audit of the simultaneous Machin-prime separator

Audit date: **2026-08-12 UTC**  
Target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt)  
Target SHA-256: 2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825  
Primary artifact: [multiprime_pulse_attack.md](multiprime_pulse_attack.md)  
Companion: [fixed_modulus_attack.md](fixed_modulus_attack.md)

## Verdict and labels

The original note had one **fatal scope error** in its broad phrases “all
simultaneous prime components” and “all overlapping prime pulses”: it
omitted a fourth, class-$5\bmod12$ pulse obtained from T47's consecutive
right- and left-endpoint forcings. Its equations were nevertheless correct
for its explicitly defined three-class T45-interior set $S_{j,L}$. During
this audit the note was narrowed accordingly. At audited SHA-256
ade5571bdd0e65a5e1c1f91798a694b24db5e24e773ce398d3b7806b8e281beb,
there is no remaining fatal error in that T45-only claim.

The fourth class changes the common-prime logarithm from
$(6-3\lambda)j+o(j)$ to $(8-4\lambda)j+o(j)$ for
$L\sim\lambda j$. It invalidates the original upper-half cofactor proof
when that proof is broadened to all four classes. A different two-band
argument repairs the all-four-class separator below.

Claim labels are exact: T45--T50 retain their recorded “machine-checked”
status. T49 now proves the new pulse, and T50 proves the two-band local seed
lemma including its endpoint case. The PNT application, CRT construction,
and Kanold construction remain “proof sketch”; finite runs are “experiment”;
the PNT/PNT-in-AP and Kanold inputs are “literature-checked” as of the audit
date. V1 remains a “conjecture”.

## 1. Missing class-5 pulse

Put

\[
 y_n=10^nM_{3n},\qquad y_{n+1}=10y_n+\Delta_n,\qquad
 C_1=\frac{4\cdot951}{5\cdot239}.
\]

Let $p=12N+17$ be prime. T47's right endpoint in $\Delta_N$ gives

\[
 py_{N+1}\equiv-\frac4{239}10^{N+1}\pmod p.       \tag{A1}
\]

The next left endpoint contributes $16\,10^{N+2}/5$, so

\[
\begin{aligned}
 py_{N+2}
 &\equiv10\left(-\frac4{239}10^{N+1}\right)
       +\frac{16}{5}10^{N+2}\\
 &\equiv C_1 10^{N+2}\pmod p.                    \tag{A2}
\end{aligned}
\]

For $p\ne317$, later forcings are $p$-integral until $3p$ reaches a
window. The largest denominator needed to reach time $N+2+t$ is
$12N+29+12t<3p=36N+51$ exactly through $t\le2N+1$. Hence

\[
 \boxed{py_{N+2+t}\equiv C_1\chi_4(p)10^{N+2+t}\pmod p,
        \quad0\le t\le2N+1.}                    \tag{A3}
\]

Here $\chi_4(p)=1$ because $p\equiv1\pmod4$. At $p=317$, the two
endpoint impulses cancel the long component since $951=3\cdot317$; the
right impulse still survives for one time. The base $239$ remains the
separate T47 base exception already frozen through its full primary factor.

On $I_{j,L}=\{j,\ldots,j+L-1\}$, the new long pulse persists exactly for

\[
 \left\lceil\frac{j+L-4}{3}\right\rceil\le N\le j-2. \tag{A4}
\]

For $L=1$, one additional transition factor $p=12j+5$ may be retained.
PNT in the class $5\bmod12$ contributes $(2-\lambda)j+o(j)$, so

\[
 \boxed{\log P^*_{j,L}=(8-4\lambda)j+o(j),\qquad
 \#S^*_{j,L}\sim(8-4\lambda)\frac j{\log j}.}     \tag{A5}
\]

All four long-pulse signs are $\chi_4(p)$. Thus the character-weighted CRT
collapse in equations (9)--(15) of the audited note extends unchanged to
$S^*_{j,L}$. The optional length-one factor uses its own local coefficient
and has no effect on (A5).

## 2. Original claims that remain valid

At the explicit T45-interior scope, the following are correct:

- pulse geometry (1)--(3);
- PNT-in-AP scales (4)--(5), including constants $6-3\lambda$ and 9;
- common-denominator scale (6)--(8);
- character/CRT collapse (9)--(15);
- upper-half cofactor and Kanold construction (16)--(25);
- exact forcing telescope and error bounds (26)--(27); and
- actual/cofactor phase decomposition (28)--(29).

The companion note freezes only the at-most-three fresh components born
from one $\Delta_N$, so its narrowed mathematical claim is unaffected.

The invalid reading was that (16)--(24) freeze every T45--T47 pulse. After
class 5 is frozen, the original upper-half argument leaves no linear
cofactor for $L\le j/2$. For $L>j/2$, it gives only

\[
 \log D\ge(4\lambda-2)j+o(j),                    \tag{A6}
\]

which beats $L\log10$ only for

\[
 \lambda>\frac2{4-\log10}=1.1782623044\ldots .   \tag{A7}
\]

So that proof cannot cover all length regimes after all four classes are
frozen.

## 3. Two-band repair

The local valuation and exact-multiplicity claims in this section are now
“machine-checked” in T50. The PNT, cofactor, and Kanold layers remain a
“proof sketch”. Write the
actual reduced seed as $y_j=a_j/Q_j$, and set $d=12j+3$. Its exact
finite expansion is

\[
 \frac{y_j}{10^j}=
 \sum_{\substack{1\le u\le d\\u\ {\rm odd}}}
 \frac{4(-1)^{(u-1)/2}(4\cdot239^u-5^u)}
      {u5^u239^u}
 -\frac4{(d+2)239^{d+2}}.                       \tag{A8}
\]

For prime $d/3<p\le d$, only $u=p$ is singular and Fermat gives

\[
 py_j\equiv10^j\chi_4(p)C_1\pmod p              \tag{A9}
\]

outside $p=239,317$. The endpoint $d+2$ cannot be a nontrivial odd
multiple of such a $p$.

For prime $d/5<p\le d/3$, only $u=p,3p$ can be singular. Their signs
are opposite, and

\[
 py_j\equiv10^j\chi_4(p)C_{13}\pmod p,           \tag{A10}
\]

where

\[
\begin{aligned}
 C_{13}
 &=4\left[\left(\frac45-\frac1{239}\right)
   -\frac13\left(\frac4{5^3}-\frac1{239^3}\right)\right]\\
 &=\frac{5359397032}{1706489875}
 =\frac{2^3\cdot11\cdot19\cdot233\cdot13757}
        {5^3\cdot239^3}.                         \tag{A11}
\end{aligned}
\]

For sufficiently large $d$, $p>d/5>\sqrt{d+2}$, so each summand has
valuation at least $-1$. A nonzero residue in (A9) or (A10) therefore
proves $v_p(y_j)=-1$, hence exact exponent one in $Q_j$.

Exact exclusions:

- bases $5,239$;
- $317$ in the upper band;
- $11,19,233,13757$ in the lower band; and
- a lower-band prime dividing $d+2$, because the unpaired endpoint then
  contributes another singular term.

The fixed primes cost $O(1)$ in logarithmic weight. For large $d$, at most
one divisor of $d+2$ exceeds $d/5$, so the coarse loss is $O(\log d)$.

Let $F^*_{j,L}$ contain the complete 5- and 239-primary factors, all
four-class long-pulse primes, and the optional length-one factor. Put
$D^*_{j,L}=Q_j/F^*_{j,L}$. Every controlled long-pulse prime obeys

\[
 p\ge4(j+L)-1.                                    \tag{A12}
\]

The new class even gives $p\ge4(j+L)+1$. Set

\[
 X=\min\{d,\,4(j+L)-2\}.                          \tag{A13}
\]

Apart from the exact exceptions, every prime $d/5<p\le X$ occurs once in
$D^*_{j,L}$. Uniformly for $1\le L\le2j+O(1)$, PNT gives

\[
 \log D^*_{j,L}\ge
 \vartheta(X)-\vartheta(d/5)-O(\log d).          \tag{A14}
\]

If $X=4(j+L)-2<d$, then

\[
 \log D^*_{j,L}-L\log10
 \ge\frac85j+(4-\log10)L+o(j)>0.                \tag{A15}
\]

If $X=d$, then

\[
 \log D^*_{j,L}-L\log10
 \ge\left(\frac{48}{5}-2\log10\right)j+o(j)>0.  \tag{A16}
\]

All denominator primes come from 5, 239, or odd linear denominators at
most $d+2$, so

\[
 \omega(D^*_{j,L})\le\pi(d+2)=o(j).              \tag{A17}
\]

Kanold's $J(D)\le2^{\omega(D)}$ and the affine-unit argument now yield

\[
 \frac{J(D^*_{j,L})}{D^*_{j,L}}<10^{-L}.         \tag{A18}
\]

Thus a reduced alternative $a'/Q_j$, with the same actual denominator and
all controlled four-class/base-primary components, exists in every
length-$L$ cylinder. Choosing $55\ldots5$ makes its exponential sum nearly
maximal. Adding the exact T38/T46 forcing preserves the common prime data
and, by the exponentially small nonnegative telescope, still avoids
$[0,0.1)$. This varies the complementary numerator; it says nothing about
the actual $a_j$ and does not imply V1.

## 4. Independent exact checks

Existing artifact hashes matched:

    92d56aa6082afec13d46cb2246adde4b9ec3dcf62c8e73c63fabdb8e9512dae4  multiprime_pulse_stats.py
    dfab08de96dde371a11a4cb5027f5b07243250a2cf2eb6c7849239d5f0e2d635  multiprime_same_modulus_check.py
    ba4d09c2abd3cd91b65b5de60d0f94a4ad569ae28649308f337ede158989c0b7  multiprime_orbit_den_gmp.cpp
    708e7ab78fdf08523ac3a6a1579f9d1859eabcee851b30839fd176f1a0726668  multiprime_orbit_den_1000.tsv

Rerun commands:

    python -m py_compile \
      work/ultrapi-resume/multiprime_pulse_stats.py \
      work/ultrapi-resume/multiprime_same_modulus_check.py

    python work/ultrapi-resume/multiprime_pulse_stats.py \
      --pair 100:50 --pair 500:250 --pair 1000:500 --pair 5000:2500

    python work/ultrapi-resume/multiprime_same_modulus_check.py \
      --min-j 2 --max-j 100

The table values were reproduced, including $\log P/j=4.5206225353$ and
upper-half complement coefficient 1.4926241742 at $(5000,2500)$. The
same-modulus run returned 394 checks and zero failures.

Independent Fraction arithmetic then:

- checked actual-seed local and propagated residues at
  $(j,L)=(5,3),(10,5),(20,10),(50,25)$;
- reproduced every numerator/denominator bit length and 5-/239-valuation
  in the retained GMP table for $0\le j\le100$;
- checked (A9)--(A11) for every eligible prime and $2\le j\le100$:
  all **7,747** assertions passed;
- directly checked the new pulse for
  $p=17,29,41,53,89,101,113,137,149$, with $317$ cancelling; and
- enlarged the same-$Q_j$ test by (A4) and the length-one factor: all
  **394** distinct checks for $2\le j\le100$ and
  $L\in\{1,\max(1,\lfloor j/2\rfloor),j,2j\}$ passed, including
  $F^*\mid Q$, coprimality, exponent one, and
  $D^*>2^{\omega(D^*)}10^L$.

The sufficient inequality fails in two $j=1$ cases, consistent with the
asymptotic claim. The host lacked gmpxx.h, so the retained C++ output beyond
100 was hash-checked but not rebuilt. The new loops were inline and have no
retained hash. All these results remain “experiment”.

Formal inputs audited by hash:

    92f773c26b348a283fb139a94d96e48ac2804af861b8013cbca6069e1584fff0  T45T45MachinPrimeSurvival.lean
    6301a9baddba9bbc9da964970560fdc19b098cfa0c10c89bee5578869f684794  T46T46MachinFixedModulusTelescoping.lean
    298565c53439c6184232b5157d351256ca17a8fcff8c9c2e5e7828d886e992d0  T47T47MachinAllPrimeSurvival.lean
    a5ee98d8842508eb81b8d8fd660441b5e0e5a4cef407318ad125d43d40249077  T49T49MachinEndpointPulse.lean
    931a50d0203ca0aa9c9d92eacf684d8d45022f8bf233dde00408a2ea25ff256c  T50T50MachinSeedLowerBandPrimeSurvival.lean

## 5. Source boundary and remaining obligation

The repair uses ordinary PNT; the product count uses fixed-modulus PNT in
arithmetic progressions. Ramaré--Rumely covers Chebyshev estimates for
modulus 12:
[Primes in arithmetic progressions](https://ramare-olivier.github.io/Maths/rumely.pdf).
The Jacobsthal input is Kanold's bound:
[Über eine zahlentheoretische Funktion von Jacobsthal](https://eudml.org/doc/161543).

The searched exponential-sum results remain inapplicable. Kerr treats one
prime modulus. Bourgain--Chang uses polynomial-size subgroups and boundedly
many suitably large factors. Here $T=\Theta(j)=\Theta(\log Q_j)$, the
number of prime factors grows, and 10 is nonunit on the 5-primary factor.

Even after all four long pulse classes are frozen, the actual complementary
residue remains uncontrolled. No estimate

\[
 \sum_{t<T}e_{Q_j}(h a_j10^t)=o(T),\qquad T\asymp j,
\]

was proved or located. No complete proof, candidate resolution, or verified
resolution of V1 is claimed.
